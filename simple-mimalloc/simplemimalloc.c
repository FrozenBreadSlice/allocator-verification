#include "simplemimalloc.h"

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
    queue, list, binning
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

//for page queues and full list in heap
u8 sm_bin (size_t size) {
    if (size > BLOCK_SIZES[SM_N_SIZE_CLASSES - 1]) return SM_N_SIZE_CLASSES;
    u8 bin = 0; 
    for (int i = 0; i < SM_N_SIZE_CLASSES; i++) {
        if (size < BLOCK_SIZES[i]) break;
        bin++;
    }
    return bin;
}

ssize_t sm_bin_to_size (u8 bin) {
    if (bin >= SM_N_SIZE_CLASSES) return -1;
    return BLOCK_SIZES[bin];
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
}
