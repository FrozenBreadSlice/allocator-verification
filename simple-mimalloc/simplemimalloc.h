#ifndef SIMPLEMIMALLOC_H
#define SIMPLEMIMALLOC_H

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

#define SM_N_SIZE_CLASSES 2
size_t BLOCK_SIZES[SM_N_SIZE_CLASSES] = {512, 1024};

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
    size_t used;      //count of pages in use 
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

void *sm_malloc (size_t size);

void sm_free (void *ptr);

#endif //SIMPLEMIMALLOC_H
