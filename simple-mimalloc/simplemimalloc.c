#include "defs.h"
#include "logger.h"
#include "assert.h"
#include <errno.h>    //errno
#include <sys/mman.h> //munmap, mmap
#include <string.h>   //strerror

/* Simple Mimalloc v1.0.0
    based on: https://github.com/microsoft/mimalloc/releases/tag/v1.0.0 
    High level design 
    - heap & segments -> pages -> blocks
    - heap manages pages and size classes/bins
        heap also holds the list of allocated segments
        for slow alloc
    - segments are large blocks of memory with metadata
    - pages are smaller units 
        free list sharding, local free list per page 
    - blocks are smallest unit and given to user
*/

//TODO(Ben): try adding another size class, (now we have one single block size / size class)
//TODO(Ben): check if arbitrary removal is only for full queue! (sm_page_queue_remove)
//  In our implementation only the full queue needs it
//  make full queue a list / different type
//  then remove arbitrary removal from queue, or keep it and type def a list type
//  in the end it is all doubly linked list anyways
//TODO(Ben): add deffered freeing
//TODO(Ben): should check that everything is freed correctly in tests: write a validation function

//NOTE: cases not handled, > largest size class
//  mimalloc has larger pages in segment for this if < 4Mib
//  otherwise it will OS allocate a segment with one page of needed size

/* NOTE: where to put segment metadata
    we kind of have options here 
    1. alocate: SM_SEGMENT_SIZE + sizeof(sm_segment_t)
        and finding page start and vice versa is more combersome
        and possibly would have to align after sm_segment_t so allocate 
        sligtly more
    2. allocate: SM_SEGMENT_SIZE 
        use first part of first page for sm_segment_t (with pages meta 
        data), this requires special handling of first page and setting 
        reserved specially, but should be doable, mimalloc v1.0.0 does this
    3. allocate: SM_SEGMENT_SIZE 
        becuase of virtual memeory we can use first part of first page 
        for segment data and then skip to next page boundary for actual 
        first page, this requires basically no special code
    effects: sm_page_init, sm_page_start, other?
*/

#define SM_SEGMENT_SIZE (4 * 1024 * 1024)
#define SM_PAGE_SIZE (64 * 1024) 

#define SM_N_PAGES_PER_SEGMENT 2 

#define SM_N_SIZE_CLASSES 1
#define SM_BLOCK_SIZE 1024

#define MAX_ALIGN 64 

struct sm_heap_t; 

/* Block
    just a node for (intrusive) freelists
*/
typedef struct sm_block_s {
    struct sm_block_s *next; 
} sm_block_t;

/* Page meda data
*/
typedef struct sm_page_t {
    u8 segment_idx;         //index in meta data pages array in segment
    bool in_full;           //page is in full bin
    u16 capacity;           //number for blocks commited (to freelist)
    u16 reserved;           //total number of blocks in this page
    sm_block_t* free;       //free-list blocks, allocation (thread-local)
    sm_block_t* local_free; //free-list blocks, freeing (thread-local)
    size_t block_size;      //size of blocks
    struct sm_heap_t *heap; //pointer to heap (for full -> free enqueueing)
    struct sm_page_t *next;
    struct sm_page_t *prev;
} sm_page_t;

/* Segment
*/
typedef struct sm_segment_t {
    struct sm_segment_t *next;
    struct sm_segment_t *prev;
    size_t used;              //count of pages in use 
    size_t info_size; //space used for segment meta data + alignment
    //NOTE: In real implementaiton this is the 'struct' ends in array
    //  trick (instead of putting it after), so indexing with segment_idx 
    //  is possible, you have 3 sizes of pages, so you don't statically know the size
    //  we have one page size, but you kind of want a variable size for larger allocation 
    sm_page_t pages[SM_N_PAGES_PER_SEGMENT]; 
} sm_segment_t;

/* Heap 
*/
typedef struct {
    sm_page_t *first;
    sm_page_t *last;
    size_t block_size;
} sm_page_queue_t;

typedef sm_page_queue_t sm_full_list_t;

//In mimalloc, it uses SM_N_SIZE_CLASSES + 1 page queues, where the last on 
//is the full list, the full list needs to support arbitrary removal
//whereas the page queues are really FIFO queues.
typedef struct sm_heap_t {
    sm_segment_t *first;
    sm_page_queue_t page_qs[SM_N_SIZE_CLASSES]; 
    sm_full_list_t full_list;
} sm_heap_t;

sm_heap_t global_heap = {0};


/* Utilities: 
    alignment calculations, etc
*/

void *sm_align_up_ptr (void *p, size_t alignment) {
    return (void*)(((uintptr_t)p + (alignment - 1)) & ~(alignment - 1));
}

size_t sm_align_up_size (size_t size, size_t alignment) {
    return (size + (alignment - 1)) & ~ (alignment - 1);
}

//page meta data is in segment, segment is 4Mb alinged so:
sm_segment_t *sm_page_to_segment (void *in_segment) {
    return (sm_segment_t*)((uintptr_t)in_segment & ~(SM_SEGMENT_SIZE - 1));
}

size_t sm_os_page_size(void) {
  static size_t page_size = 0;
  if (page_size == 0) {
    long result = sysconf(_SC_PAGESIZE);
    page_size = (result > 0 ? (size_t)result : 4096);
  }
  return page_size;
}

/* Utilities data structures: 
    intrusive stack, queue, list, etc
*/

//for freelists in pages &page->free and &page->local_free
void sm_block_push_front (sm_block_t **head, sm_block_t *new) {
    new->next = *head;
    *head = new;
}

sm_block_t *sm_block_pop_front (sm_block_t **head) {
    if (*head == NULL) return NULL;
    sm_block_t *popped = *head;
    *head = (*head)->next;
    popped->next = NULL;
    return popped;
}

//for segment list in heap->first
void sm_segment_push_front (sm_segment_t **head, sm_segment_t *new) {
    new->next = *head;
    *head = new;
}

void sm_segment_remove (sm_segment_t **head, sm_segment_t *seg) {
    if (seg->prev) seg->prev->next = seg->next;
    if (seg->next) seg->next->prev = seg->prev;
    if (seg == *head) *head = seg->next;
    seg->next = NULL;
    seg->prev = NULL;
}

//for page queues and full list in heap
u8 sm_bin (size_t size) {
    if (size > SM_BLOCK_SIZE) {
        return SM_N_SIZE_CLASSES;
    }
    return 0;
}

ssize_t sm_bin_to_size (u8 bin) {
    if (bin == 0) {
        return SM_BLOCK_SIZE;
    }
    return -1;
}

void sm_page_queue_enqueue (sm_page_queue_t *queue, sm_page_t *page_md) { 
    page_md->next = queue->first;
    page_md->prev = NULL;
    if (queue->first) {
        queue->first->prev = page_md;
        queue->first = page_md;
    } else {
        queue->first = page_md; 
        queue->last = page_md;
    }
}

//NOTE: for full list we need arbitrary removal, so not a queue
void sm_full_list_remove (sm_full_list_t *list, sm_page_t *page_md) {
    if (page_md->prev != NULL) page_md->prev->next = page_md->next;
    if (page_md->next != NULL) page_md->next->prev = page_md->prev;
    if (page_md == list->last) list->last = page_md->prev;
    if (page_md == list->first) list->first = page_md->next;
    page_md->next = NULL;
    page_md->prev = NULL;
}

//NOTE: we implement it in terms of arbitary removal for now
sm_page_t *sm_page_queue_dequeue (sm_page_queue_t *queue) {
    sm_page_t *last = queue->last;
    sm_full_list_remove(queue, last);
    return last;
}



/*
    OS: the slow os allocation operations
*/

internal bool sm_munmap(void* addr, size_t size) {
    if (!addr || size == 0) return true;
    bool err = (munmap(addr, size) == -1);
    if (err) {
        SMWARN("munmap failed: %s, addr 0x%8li, size %lu\n", 
                strerror(errno), (size_t)addr, size);
        return false;
    } 
    return true;
}

internal void* sm_mmap(void* addr, size_t size) {
    if (size == 0) return NULL;
    //for this process, not backed by file and 0 initilaized
    int flags = MAP_PRIVATE | MAP_ANONYMOUS;
    //read and write only
    int pflags = PROT_READ | PROT_WRITE;
    void* p = mmap(addr, size, pflags, flags, -1, 0);
    if (p == MAP_FAILED) p = NULL;
    if (addr && p != addr) {
        sm_munmap(p, size);
        p = NULL;
    }
    SMASSERT(!p || (!addr && p != addr) || (addr && p == addr));
    return p;
}

//Slow but guaranteed way to allocated aligned memory
//by over-allocating and then reallocating at a fixed aligned
//address that should be available then.
void *sm_os_alloc_aligned(size_t size, size_t alignment) {
    size_t alloc_size = size + alignment;
    SMASSERT(alloc_size >= size); 
    if (alloc_size < size) return NULL;

    //allocate a chunk that includes the alignment
    void* p = sm_mmap(NULL, alloc_size);
    if (!p) return NULL;
    //create an aligned pointer in the allocated area
    void* aligned_p = sm_align_up_ptr(p, alignment);
    SMASSERT(aligned_p);
    //we selectively unmap parts around the over-allocated area.
    size_t pre_size = (uint8_t*)aligned_p - (uint8_t*)p;
    size_t mid_size = sm_align_up_size(size, sm_os_page_size());
    size_t post_size = alloc_size - pre_size - mid_size;
    if (pre_size > 0)  sm_munmap(p, pre_size);
    if (post_size > 0) sm_munmap((uint8_t*)aligned_p + mid_size, post_size);
    SMASSERT(((uintptr_t)aligned_p) % alignment == 0);
    return aligned_p;
}


/*
    Page
*/ 

bool sm_page_is_first_of_segment (sm_segment_t *segment, sm_page_t *page_md) {
    SMASSERT(segment && page_md)
    return &segment->pages[0] == page_md; 
}

bool sm_page_init (sm_heap_t *heap, sm_page_t *page_md, size_t block_size, size_t idx) {
    page_md->segment_idx = idx; //mi_page_init doesn't set this one, for some reason 
    page_md->in_full = false;
    page_md->capacity = 0;
    
    //first page is smaller since we fit the segment data in there, see _mi_segment_page_start, mi_page_init 
    sm_segment_t *segment = sm_page_to_segment(page_md); 
    if (!segment) return false;
    if (sm_page_is_first_of_segment(segment, page_md)) {
        page_md->reserved = (SM_PAGE_SIZE - segment->info_size) / block_size;
    } else {
        page_md->reserved = SM_PAGE_SIZE / block_size;
    }
    
    page_md->free = NULL;
    page_md->local_free = NULL;
    page_md->block_size = block_size;
    page_md->heap = heap;
    return true;
}

//find actual page start from the (sm_page_t page_md) meta data
//the first page is smaller, since its beginning is taken up by 
void *sm_page_start (sm_segment_t *segment, sm_page_t *page_md) {
    if (sm_page_is_first_of_segment(segment, page_md)) {
        return ((u8*)segment + segment->info_size);
    }
    return (void*)((u8*)segment + page_md->segment_idx * SM_PAGE_SIZE);
}

//this funtion initalizes freelist nodes on demand
void sm_page_extend_free (sm_page_t *page_md) {
    if (!page_md) return;
    SMASSERT(page_md->capacity <= page_md->reserved);

    if (page_md->capacity == page_md->reserved) return;
    //mimalloc does something different, not exponential like this
    size_t extend = page_md->capacity < 1 ? 1 : page_md->capacity;
    if (page_md->capacity + extend > page_md->reserved) {
        extend = page_md->reserved - page_md->capacity; 
    }
    //we need start of actual page, first page is special case :|
    void *page = sm_page_start(sm_page_to_segment(page_md), page_md);
    //now we need to go until after our current capacity
    u8 *start = (u8*)page + page_md->capacity * page_md->block_size;
    for (size_t i = 0; i < extend; i++) {
        sm_block_t *block = (sm_block_t*)(start + i * page_md->block_size);
        sm_block_push_front(&page_md->free, block);
    }
    page_md->capacity += extend;
}

//_mi_page_unfull
void sm_page_to_class (sm_page_t *page_md) {
    SMASSERT(page_md->in_full)
    sm_heap_t *heap = page_md->heap; 

    //calculate queue from heap and page
    sm_page_queue_t *toq = &heap->page_qs[sm_bin(page_md->block_size)];    
    
    //remove from full_list add to toq 
    sm_full_list_remove(&heap->full_list, page_md); 
    page_md->in_full = false;
    sm_page_queue_enqueue(toq, page_md);
}

void sm_page_to_full (sm_page_queue_t *queue) {
    sm_page_t *page_md = sm_page_queue_dequeue(queue); 
    sm_heap_t *heap = page_md->heap; 
    SMASSERT(!page_md->in_full)

    sm_page_queue_enqueue(&heap->full_list, page_md);
    page_md->in_full = true;
}


/* 
   Segment 
*/

sm_segment_t *sm_segment_allocate () {
    //NOTE: in real implementeation both are SM_SEGMENT_SIZE, but this is better for testing
    return sm_os_alloc_aligned(SM_PAGE_SIZE * SM_N_PAGES_PER_SEGMENT, SM_SEGMENT_SIZE); 
}

void sm_segment_init (sm_heap_t *heap, sm_segment_t *segment) {
    size_t info_size = sm_align_up_size(sizeof(sm_segment_t), MAX_ALIGN);
    segment->info_size = info_size; 
    segment->used = 0;
    sm_segment_push_front(&heap->first, segment);
    //NOTE: pages are initialzed when they are needed! (see sm_heap_malloc)
}


/*
    Heap
*/

void *sm_heap_malloc (sm_heap_t *heap, size_t size) {
    u8 bin = sm_bin(size);
    //NOTE: fail if trying to allocate more then biggest size class
    //  mimalloc's largest size class is approximatly the segment size 
    //  for larger allocations it will just OS allocate a segment of requested size and also on freeing it unmaps 
    if (bin >= SM_N_SIZE_CLASSES) return false; 
    sm_page_queue_t *queue = &heap->page_qs[bin];

    sm_page_t *page = queue->last;
    sm_block_t *free_block = NULL;
    while (page) {
        SMDEBUG("Found page in queue\n")
        //0. find free block in page
        free_block = sm_block_pop_front(&page->free);
        if (free_block) { 
            SMDEBUG("Found block in page freelist\n")
            break;
        }

        //1. try to collect freed blocks, page->free_local to page->free
        //NOTE: in mimalloc this is basically done sm_page_free_collect(page) but also with the thread_free list
        page->free = page->local_free;
        page->local_free = NULL;
        free_block = sm_block_pop_front(&page->free);
        if (free_block) {
            SMDEBUG("Found block in page after swapping free and free_local\n");
            break;
        }

        //2. try extending page, page->free is initialized on demand
        sm_page_extend_free(page);
        free_block = sm_block_pop_front(&page->free);
        if (free_block) {
            SMDEBUG("Found block in page after page extending\n");
            break;
        }

        //3. page is full: move to full, so alloc from queue remains fast 
        SMDEBUG("Page is full, removing from queue, adding to full bin\n")
        SMASSERT(page == queue->last) //just in case
        sm_page_to_full(queue); 

        page = queue->last;
    }
    
    if (!free_block) {
        SMDEBUG("Could not find block, looking for segments\n")
        //TODO(Ben): 1. do deffered freeing

        //NOTE: i believe in mimalloc 
        //  segments don't reclaim empty pages 
        //  they just stay in heap bins, only on thread death
        //  does any recliaming happen
        //  maybe we should add a freelist or something to segments for pages? or is this ok?

        //2. finding fresh page and allocate a block 
        //NOTE: here i did the simplest thing
        //  we loop over every segment to find a page using heap linked list of segments
        //  TODO(Ben): how exactly does mimalloc do this?
        sm_segment_t *segment = heap->first;
        while (segment) {
            if (segment->used < SM_N_PAGES_PER_SEGMENT) {
                SMDEBUG("Found segment with available page\n")
                page = &segment->pages[segment->used];
                segment->used++;
                break;
            }
            segment = segment->next;
        }

        if (page) {
            SMDEBUG("Enqueueing new page, initializing it, page extending it and getting a block from it\n")
            sm_page_init(heap, page, sm_bin_to_size(bin), segment->used - 1);
            sm_page_queue_enqueue(queue, page);
            sm_page_extend_free(page);
            free_block = sm_block_pop_front(&page->free);
            if (free_block) return free_block;
        }

        //3. allocate a new segment and get a page and allocate a block
        SMDEBUG("OS allocating new segment\n")
        segment = sm_segment_allocate(); 
        if (!segment) {
            SMDEBUG("Could not OS allocate segment, sm_malloc failed\n")
            return NULL;
        }
        sm_segment_init(heap, segment);
        page = &segment->pages[segment->used];
        segment->used++;

        if (page) {
            SMDEBUG("Enqueueing new page, initializing it, page extending it and getting a block from it\n")
            sm_page_init(heap, page, sm_bin_to_size(bin), segment->used - 1);
            sm_page_queue_enqueue(queue, page);
            sm_page_extend_free(page);
            free_block = sm_block_pop_front(&page->free);
        }
    }

    return free_block; 
}


/*
   Alloc and free
*/

void *sm_malloc (size_t size) {
    SMDEBUG("New sm_malloc call:\n")
    return sm_heap_malloc(&global_heap, size);
}

void sm_free (void *ptr) {
    sm_segment_t *segment = sm_page_to_segment(ptr); 
    uintptr_t res = (uintptr_t)ptr - (uintptr_t)segment;
    size_t page_idx = res / SM_PAGE_SIZE;
    sm_page_t *page_md = &segment->pages[page_idx];
    if (page_md->in_full) { 
        SMDEBUG("Returning previously full page to size class bin\n") 
        sm_page_to_class(page_md);  
    }
    sm_block_push_front(&page_md->local_free, (sm_block_t*)ptr);
    //deffered freeing?
}

/*
    Main
*/

i32 main () {
    /* Test 1: allocate and free 
        all the way slow path: os allocate first segment
    */
    SMDEBUG("----------TEST 1-----------\n")
    void *data = sm_malloc(500);  
    sm_free(data);
    SMDEBUG("--------------------------\n")

    /* Test 2: allocate and free multiple times 
        should always return the same block
        since it should collect free blocks first: (page->free = page->local_free)
        only after that it page extends: which should not be hit.
    */
    SMDEBUG("----------TEST 2-----------\n")
    int enough = SM_SEGMENT_SIZE / SM_PAGE_SIZE + 1;
    void *prev = data;
    for (int i = 0; i < enough; i++) {
        data = sm_malloc(500);
        SMASSERT(prev == data)
        prev = data;
        sm_free(data);
    }
    SMDEBUG("--------------------------\n")

    /* Test 3: allocate enough to page extend multiple times  
        it should extend 4 times: 1 -> 2, 2 -> 4, 4 -> 8, 8 -> 16 
    */ 
    SMDEBUG("----------TEST 3-----------\n")
    void *datas[10];
    for (int i = 0; i < 10; i++) {
        datas[i] = sm_malloc(500);
    }
    for (int i = 0; i < 10; i++) {
        sm_free(datas[i]);
    }
    SMASSERT(global_heap.first->pages[0].capacity == 16)
    SMDEBUG("--------------------------\n")

    /* Test 4: allocate enough to ask for new page 
        first page has 63 blocks (due to segment/page metadata)  
        so we will allocate 64 times  
        - since everything is freed before we should be able to allocate 10 times 
            from fee list first, then 6 more times from last page extend
        - then we page extend from 16 -> 32 and 32 -> 63
        - on 64th allocation it will put the page into the full bin
            and if SM_N_PAGES_PER_SEGMENT == 1 
            then allocate a new os segment 
            otherwise allocate a new page from segment. 
        - on the second to last free it should also return the full page to the size class queue/stack 
    */
    SMDEBUG("----------TEST 4-----------\n")
    void *datas2[64];
    for (int i = 0; i < 64; i++) {
        datas[i] = sm_malloc(500);
    }
    for (int i = 0; i < 64; i++) {
        sm_free(datas[i]);
    }
    //if there is one page per segment, a new segment was allocated and put as global-heap.first
    if (SM_N_PAGES_PER_SEGMENT == 1) {
        SMASSERT(global_heap.first->next->pages[0].capacity == global_heap.first->next->pages[0].reserved)
    } else {
        SMASSERT(global_heap.first->pages[0].capacity == global_heap.first->pages[0].reserved)
    }
    SMDEBUG("--------------------------\n")

    return 0;
}
