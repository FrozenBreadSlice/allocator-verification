# High level description mimalloc v1.0.0
Most important types/concepts.
The paper and source code here only talk about mimalloc v1.0.0!

NOTE: Weird data race behaviour: 
    there are a few places where mimcalloc allows data races to happen to make it faster 
    then in the slow path it recovers from it for example the `thread_freed` variable is not atomically updated
    `volatile uintptr_t    thread_freed;      // at least this number of blocks are in thread_free`
    why is it a `uintptr_t` anyways, when `used` is a `size_t`?

- heap (`mi_heap_t`): 
    this keeps track of the size classes and pages that belong to those classes
    heaps are bound to threads
    ```
    typedef struct {
        //TODO(Ben): thread local data is needed if we do multithreading
        //except if we only have one thread that allocates, and others only free?
        //mi_tld_t*           tld;
        mi_page_t*            pages_free_direct[MI_SMALL_WSIZE_MAX + 2];   
        mi_page_queue_t       pages[MI_BIN_FULL + 1];         // queue of pages for each size class (or "bin")
        volatile mi_block_t*  thread_delayed_free;
        uintptr_t             thread_id;                      // thread this heap belongs too
        size_t                page_count;                     // total number of pages in the `pages` queues.
        bool                  no_reclaim;                     // `true` if this heap should not reclaim abandoned pages
    } mi_heap_t;
    ```
    I did some simplifications, removed some security hardening features such as cookies.

- segment (`mi_segment_t`): 
    this keeps track of virtual memory mapped spaces (4Mib) and devides 
    them into pages.
    I don't know where the segment metadata is stored since I believe the 
    mmaps are always extacly 4Mibs but this 4Mibs is also exactly devided over 
    64 pages of 64Kibs. (TODO(Ben): figure this out)
    segments are bound to threads
    this type doesn't exist in current main branch 
    I think it is replaced by/renamed with `mi_arena_t` 
    there are probably some more differences.
    An interesting thing is when threads finish or are killed, 
    the segments will still have unclaimed virutual memory spaces 
    so on exit of a thread mimalloc will put the segments or pages in an 
    abandonned list (TODO(Ben): in tld?)
    ```
    typedef struct mi_segment_s {
        struct mi_segment_s* next;
        struct mi_segment_s* prev;
        struct mi_segment_s* abandoned_next;
        //TODO(Ben): if we do multithreaded then we do have to deal with abandoned pages..
        //size_t          abandoned;   // abandoned pages (i.e. the original owning thread stopped) (`abandoned <= used`)
        size_t          used;        // count of pages in use (`used <= capacity`)
        size_t          capacity;    // count of available pages (`#free + used`)
        size_t          segment_size;

        // `1 << page_shift` == the page sizes == `page->block_size * page->reserved` 
        //(unless the first page, then `-segment_info_size`).
        size_t          page_shift;  
        uintptr_t       thread_id;   // unique id of the thread owning this segment
        mi_page_t       pages[1];    // up to `MI_SMALL_PAGES_PER_SEGMENT` pages
    } mi_segment_t;
    ```
    Again made some simplificaton I think I can make.

- page (`mi_page_t`):
    this is a unit of memory bound to a size class and conttains same 
    sized blocks and 3 freelists.
    So instead of each size class having a large space of same sized blocks 
    with one freelist the size classes have multiple linked pages
    with their own free lists, this makes spacial locality better when allocating.
    Since links in a freelist could be very far appart and jump around a lot.

    There are 3 freelists, 
    The `page->free` (`mi_block_t*`) freelist is used only for allocating 
    The `page->local_free` (`mi_block_t*`) freelist is for 
        the same thread to free to 
    The `page->thread_free` freelist is used for other threads to free to. 
        The type of `page->thread_free` is kind of strange 
        and I don't fully understand it 
        (TODO(Ben): would (`mi_block_t*`) suffice as a simplification? I doubt it)

    This is done so that atomics/locks are only necessary for the third list, 
    The first two lists don't need any synchronisation.

    Mimalloc allocates and frees from different freelists because it 
    wants to hit the slow path consistently. After finitely many 
    allocations the first free list will be empty and thus the slow 
    path will be hit. Mimialloc wants this becuase in the slow 
    path deferred freeing is handled, which is a feature wanted by 
    many language runtimes with deep pointer trees, to not make freeing 
    a huge stop-the-world kind of thing.
    Also in the slowpath the `local_free` and `thread_free` lists are 
    appended and assigned to the `free` freelist, so 
    that allocation in the page is possible again.
    ```
    typedef struct mi_page_t {
        // "owned" by the segment
        u8               segment_idx;     // index in the segment `pages` array, `page == &segment->pages[page->segment_idx]`
        bool             segment_in_use;  // `true` if the segment allocated this page
        bool             is_reset;        // `true` if the page memory was reset

        //TODO(Ben): what to do with this flags?
        //mi_page_flags_t  flags; 
        u16              capacity;          // number of blocks committed
        u16              reserved;          // numbes of blocks reserved in memory

        mi_block_t*           free;           // list of available free blocks (`malloc` allocates from this list)
        size_t                used;           // number of blocks in use (including blocks in `local_free` and `thread_free`)

        mi_block_t*           local_free;     // list of deferred free blocks by this thread (migrates to `free`)
        volatile uintptr_t    thread_freed;   // at least this number of blocks are in `thread_free`
                                              //TODO(Ben): some sort of packed pionter that also holds other stuff see mimalloc-types.h, what to do with?
        //volatile mi_thread_free_t thread_free;   // list of deferred free blocks freed by other threads
        volatile uintptr_t thread_free;

        // less accessed info
        size_t                block_size;     // size available in each block (always `>0`)
        struct mi_heap_t*     heap;           // the owning heap
        struct mi_page_t*     next;           // next page owned by this thread with the same `block_size`
        struct mi_page_t*     prev;           // previous page owned by this thread with the same `block_size`
        //TODO(Ben): need to add padding back?
    } mi_page_t;
    ```
    
- block (`mi_block_t`):
    Same sized blocks with next pointer, but 
    in the mimalloc source they are encoded? 
    I guess next is not directly used as a pointer but 
    it is subdivided or somethig like that.
    ```
    //TODO(Ben): why was named mt_encoded_t?, just make pointer?
    typedef uintptr_t mi_encoded_t;
    typedef struct mi_block_t {
        mi_encoded_t next; 
    } mi_block_t;
    ```

# Tracing mimalloc v1.0.0 using gdb
first malloc, slow path, all the way to mmap (on linux)
```
void *data = malloc(10);
```

## Step 1: `mi_malloc(size)`
- At alloc.c:~111 
    ```
    extern inline void* mi_malloc(size_t size) mi_attr_noexcept {
      return mi_heap_malloc(mi_get_default_heap(), size);
    }
    ```
    allocating a block of sufficient size.

- Go to Step 2: `mi_heap_malloc(heap, size)`

> Returned from Step 2: not interesting 

TODO(Ben): How did the size class stuff happen with heap, i completely missed that?

---

## Step 2: `mi_heap_malloc(heap, size)`
- At alloc.c:91
    ```
    extern inline void* mi_heap_malloc(mi_heap_t* heap, size_t size) {...}
    ```
    allocating a block of sufficient size.

- Important code 
    ```
    #define MI_SMALL_SIZEMAX = (128 * sizeof(void*)) (mimalloc-internal.h)
    void *p;
    p = size <= MI_SMALL_SIZEMAX ? mi_heap_malloc_small(heap, size) : _mi_malloc_generic(heap, size);
    return p;
    ```    
    Either calls:
    * `mi_heap_malloc_small(heap, size)`, 
        which is potentially the fast path, altough this will still 
        call `_mi_malloc_generic` if fast path fails
    * `_mi_malloc_generic(heap, size)`, 
        slow path

- Go to Step 3: `_mi_heap_get_free_small_page`
    this will also hit `mi_malloc_generic` in our case

> Returned from Step 3: just returns pointer p. 

---

## Step 3: `mi_heap_malloc_small(heap, size)`
- At alloc.c:~70 
    ```
    extern inline void* mi_heap_malloc_small(mi_heap_t* heap, size_t size) mi_attr_noexcept {
      mi_page_t* page = _mi_heap_get_free_small_page(heap,size);
      return _mi_page_malloc(heap, page, size);
    }
    ```
    allocates small block, pages are made out of same sized blocks!

- Important code 
    * `_mi_heap_get_free_small_page(heap, size) = heap->pages_free_direct[_mi_wsize_from_size(size)];`
        this is just a getter for direct free pages the heap has
    * `_mi_wsize_from_size(size) = (size + sizeof(uintptr_t) - 1) / sizeof(uintptr_t);`
        this rounds to nearest amount of words, on (64 bit, 8 byte words)
        meaning our index becomes (10 (size) + 8 - 1 / 2) = 2, 
        so we index `pages_free_direct` with 2.
    * both of these funciton live in mimalloc-internal.h

- Go to Step 4: `_mi_page_malloc(heap, page, size)`
    
> Returned from Step 4: not interesting 

TODO(Ben): look into this more, how exatcly are the size classes organized?

---

## Step 4: `_mi_page_malloc(heap, page, size)` 
- alloc.c:~20
    ```
    extern inline void* _mi_page_malloc(mi_heap_t* heap, mi_page_t* page, size_t size) mi_attr_noexcept {...}
    ```
    fast allocation in a page: just pop from the free list.
    fall back to generic allocation only if the list is empty.

- Important code 
    ```
    mi_block_t* block = page->free;
    if (block == NULL) return _mi_malloc_generic(heap, size); // slow path
    page->free = mi_block_next(page,block);                   // pop from the free list
    page->used++;
    return block;
    ```
    On first run `block = page->free = NULL`
    so we do `_mi_malloc_generic(heap, size)`, which will 
    try to allocate and return a block.

> Return From Step 5:
    * Step 5: `_mi_malloc_generic(heap, size)` calls this function again, so we start from top and 
        now `page->free` should not be NULL, pretty sure an assert would crash the program if tis is not the case 
        at this point so it can never call `_mi_malloc_generic(heap, size)` again from this function.
    * Now with `page->free` valid
        we get to `mi_block_next`, with hardening this is encoded with the cookie but 
        for us it is just `block->next`, `page->used++` is for #used blocks in page

---

# Step 5: `_mi_malloc_generic(heap, size)`
- page.c:~685 (we left alloc.c)
    ```
    void* _mi_malloc_generic(mi_heap_t* heap, size_t size) mi_attr_noexcept {...}
    ```
    generic allocation routine if the fast path Step 4: `mi_page_malloc` (alloc.c) does not succeed.
    or for large allocations called form Step 2: `mi_heap_malloc` (alloc.c) 
    for our purposes allocations < 8Kib (`MI_SMALL_SIZEMAX`)

- Important code:
    ```
    //initialize heap if necessary (not shown)
    _mi_deferred_free(heap, false);
    
    mi_page t* page = size > MI_LARGE_SIZE_MAX ? mi_huge_page_alloc(heap,size) : mi_find_free_page(heap,size);
    if (page == NULL) return NULL;            // out of memory

    return _mi_page_malloc(heap, page, size); // to Step 4! and try again, this time succeeding! (i.e. this should never recurse)
    ```
    * `mi_heap_is_initialized` should return true since before main 
        `mi_process_init` is called which inits heap? 
    * `_mi_deferred_free(heap, false);`, calls potential deferred free routines
        these are user defined routines mentioned in the paper.
        The nice thing is that for consistant performance mimalloc only frees so 
        much and keeps a `deffered_free` list, usefull for large pointer chains 
        escpecially when dealing with ref counting language runtimes.
    * `MI_LARGE_SIZE_MAX` is 512kb on 64-bit
    ```mimalloc-types.h
    #define MI_INTPTR_SHIFT 3
    #define MI_SMALL_PAGE_SHIFT               (13 + MI_INTPTR_SHIFT)      // 64kb
    #define MI_LARGE_PAGE_SHIFT               ( 6 + MI_SMALL_PAGE_SHIFT)  // 4mb
    #define MI_SEGMENT_SHIFT                  ( MI_LARGE_PAGE_SHIFT)      // 4mb
    // Derived constants
    #define MI_SEGMENT_SIZE                   (1<<MI_SEGMENT_SHIFT)
    #define MI_SEGMENT_MASK                   ((uintptr_t)MI_SEGMENT_SIZE - 1)

    #define MI_SMALL_PAGE_SIZE                (1<<MI_SMALL_PAGE_SHIFT)
    #define MI_LARGE_PAGE_SIZE                (1<<MI_LARGE_PAGE_SHIFT)

    #define MI_SMALL_PAGES_PER_SEGMENT        (MI_SEGMENT_SIZE/MI_SMALL_PAGE_SIZE)
    #define MI_LARGE_PAGES_PER_SEGMENT        (MI_SEGMENT_SIZE/MI_LARGE_PAGE_SIZE)

    #define MI_LARGE_SIZE_MAX                 (MI_LARGE_PAGE_SIZE/8)   // 512kb on 64-bit
    #define MI_LARGE_WSIZE_MAX                (MI_LARGE_SIZE_MAX>>MI_INTPTR_SHIFT)

    // Maximum number of size classes. (spaced exponentially in 16.7% increments)
    #define MI_BIN_HUGE  (64U)
    #define MI_MAX_ALIGN_SIZE  16   // sizeof(max_align_t)
    ```
    * TODO(Ben): maybe look at `mi_huge_page_alloc`, but should just boil down ot mmap call
    * `mi_find_free_page(heap, size)` 
        if size is less then 512Kib find a page with free blocks in our size segregated queues
        (Step 6) 

- Go to Step 6: `mi_find_free_page(heap,size)`


> Returned from Step 6.
    TODO(Ben): tidy up this explanation
    //from `mi_find_free_page` we did the whole story now we `_mi_page_alloc` again 
    //but now we have a page (alloc.c:25)

---

## Step 6: `mi_find_free_page(heap, size)`
- At page.c:~630
    ```
    static inline mi_page_t* mi_find_free_page(mi_heap_t* heap, size_t size) {...}
    ```
    find a page with free blocks in appropriate size class 

- Important code: 
    ```
    _mi_heap_delayed_free(heap);                    
    mi_page_queue_t* pq = mi_page_queue(heap,size); 
    mi_page_t* page = pq->first;
    if (page != NULL) {
        _mi_page_free_collect(page);
        if (mi_page_immediate_available(page)) return page; // fast path 
    }
    return mi_page_queue_find_free_ex(heap, pq);
    ```
    * `mi_heap_delayed_free(heap);`
        not sure what this is doing? maybe reclaiming pages from dead threads?
    * `mi_page_queue(heap,size);`
        this is in mimalloc-interval.h 
        it boils down to this:
        `mi_page_internal(heap, size) := &heap->pages[_mi_bin(size)];`
        and `_mi_bin_(size)` decides the size class that `size` is a part of
        it first calculates the amound of words `size` fits in. (`_wi_wsize_from_size`)
        for size = 10 -> 2 words
        then if 
        wsize <= 8 -> bin = wsize
        (with alignment it is rounded up by 2 or 4 to skip some bins)
        for wsize > 8, multiple wordsizes to the same bin, logarithmic I suppose. 
        At the end you have a queue having pages form a particular size class!
    * Our page is null so we go to `mi_page_queue_find_free_ex(heap, pq)` Step 7.

- Go to Step 7: `mi_page_queue_find_free_ex(heap, pq)`

> Returned from Step 7: not interesting 

TODO(Ben): why a queue and not a list? does paper answer this?

---

## Step 7: `mi_page_queue_find_free_ex(heap, pq)`
- At page.c:~560
    ```
    static mi_page_t* mi_page_queue_find_free_ex(mi_heap_t* heap, mi_page_queue_t* pq) {...}
    ```
    find a page with free blocks (of `page->block_size`) in the queue
    we are already in the right size class/page queue in the heap

- Important code 
    * this function itterates over all pages in the queue 
        until it finds a page that has a free block
    * Our queue head `pq->first` is Null so we move on to
        `mi_page_fresh(heap, pq);` which is called to 
        get a new page for this size class
        
- Go to

> Returned from Step 8: TODO(Ben): fill in 

## Step 8: 
- At page.c:~230
    ```
    static mi_page_t* mi_page_fresh(mi_heap_t* heap, mi_page_queue_t* pq) {...}
    ```
    get a fresh page to use from a segment, 
    we either reclaim a thread abandoned segment (if the `heap->no_reclaim` is not set) 
    otherwise we allocate a new segment

- Important code
    ```
    mi_page_t* page = pq->first;
    if (!heap->no_reclaim &&
        _mi_segment_try_reclaim_abandoned(heap, false, &heap->tld->segments) &&
        page != pq->first)
    {
        page = pq->first;
        if (page->free != NULL) return page;
    }
    page = mi_page_fresh_alloc(heap, pq, pq->block_size);   // otherwise allocate the page
    if (page==NULL) return NULL;
    return page;
    ```
    * TODO(Ben): we skip reclaiming logic for now
    * We move to `mi_page_fresh_alloc(heap, pq, block_size)` Step 9.

- Go to Step 9: `mi_page_fresh_alloc(heap, pq, block_size)`

> Returned from Step 9: not interesting 

---

## Step 9: `mi_page_fresh_alloc(heap, pq, block_size)`
- At page.c:~210
    ```
    static mi_page_t* mi_page_fresh_alloc(mi_heap_t* heap, mi_page_queue_t* pq, size_t block_size) {...}
    ```
    allocate fresh page from a segment 

- Important code
    ```
    mi_page_t* page = _mi_segment_page_alloc(block_size, &heap->tld->segments, &heap->tld->os);
    if (page == NULL) return NULL;
    mi_page_init(heap, page, block_size, &heap->tld->stats);
    mi_page_queue_push(heap, pq, page);
    return page;
    ```
    * We unconditionally jump to `_mi_segment_page_alloc(block_size, segments, os)`
        so `heap->tld` holds `segments`

- Go to Step 10: `_mi_segment_page_alloc(block_size, segments, os)`

> Returned from Step 10 
    * `mi_page_init` is relatively straightforward, it asserts more then it does
    * `mi_page_queue_push` is also what you would expect

---

NOTE: THIS STEP COULD BE EASILY REMOVED IF WE JUST ASSUME 1 PAGE SIZE

## Step 10: `_mi_segment_page_alloc(block_size, segments, os)`
- At segment.c:~700  
    ```
    mi_page_t* _mi_segment_page_alloc(size_t block_size, mi_segments_tld_t* tld, mi_os_tld_t* os_tld) {...}
    ```
    allocate a small, large or huge page from a segment

- Important code
    ```
    mi_page_t* page;
    if (block_size < MI_SMALL_PAGE_SIZE / 8) // smaller blocks than 8kb (assuming MI_SMALL_PAGE_SIZE == 64kb)
        page = mi_segment_small_page_alloc(tld,os_tld);
    else if (block_size < (MI_LARGE_SIZE_MAX - sizeof(mi_segment_t)))
        page = mi_segment_large_page_alloc(tld, os_tld);
    else
        page = mi_segment_huge_page_alloc(block_size,tld,os_tld);
    return page;
    ```
    * We goto `mi_segment_small_page_alloc(tld, os_tld)`

- Go to Step 11: `mi_segment_small_page_alloc(tld, os_tld)`

> Returned from Step 11: not interesting

---

## Step 11: `mi_segment_small_page_alloc(tld, os_tld)`
- At segment.c:~670
    ```
    static mi_page_t* mi_segment_small_page_alloc(mi_segments_tld_t* tld, mi_os_tld_t* os_tld) {...}
    ```
    allocate 

- Important code 
    ```
    if (mi_segment_queue_is_empty(&tld->small_free)) {
        mi_segment_t* segment = mi_segment_alloc(0,MI_PAGE_SMALL,MI_SMALL_PAGE_SHIFT,tld,os_tld);
        if (segment == NULL) return NULL;
        mi_segment_enqueue(&tld->small_free, segment);
    }
    return mi_segment_small_page_alloc_in(tld->small_free.first,tld);
    ```
    * `mi_segment_queue_is_empty(small_free) := small_free->first == NULL` 
        here `small_free : mi_segment_queue_t`
        this is indeed null so we are going to alloc a segment

- Go to Step 12: `mi_segment_alloc(0,MI_PAGE_SMALL,MI_SMALL_PAGE_SHIFT,tld,os_tld)`

> Returned from Step 12: `mi_segment_alloc(0,MI_PAGE_SMALL,MI_SMALL_PAGE_SHIFT,tld,os_tld)`
    TODO(Ben): tidy this up
    * //there we actually allocate from OS it seems
        //we get back and 4MiB segment initialized
    * `mi_segment_small_page_alloc_in(segment_queue, tld);`
        //so we enqueue sgement to the thread local data (tdl) small free list?
        //enqueue: segment.c 99

---

## Step 12: `mi_segment_alloc(0,MI_PAGE_SMALL,MI_SMALL_PAGE_SHIFT,tld,os_tld)`
- At segment.c:~ 
    ```
    static mi_segment_t* mi_segment_alloc(size_t required, mi_page_kind_t page_kind, 
                                          size_t page_shift, mi_segments_tld_t* tld, 
                                          mi_os_tld_t* os_tld) {...}
    ```
    allocate a segment from the OS aligned to `MI_SEGMENT_SIZE`.
    most notable here is that the alignment is huge: `MI_SEGMENT_SIZE = 4194304` (4Mib)
    this is only feasible due to virtual memory

    TODO(Ben): I remember paper saying these huge alignments are used 
        since page meta data is in segments and this way from a page 
        you can easily calculate start of segment?
    TODO(Ben): still where is segment meta data stored?

- Important code
    Code here is more simplified then in most other steps
    ```
    size_t page_size = (size_t)1 << page_shift;
    size_t capacity = MI_SEGMENT_SIZE / page_size;
    size_t info_size;
    size_t pre_size;
    size_t segment_size = mi_segment_size(capacity, required, &pre_size, &info_size);

    // Allocate the segment
    mi_segment_t* segment = NULL;

    // try to get it from our caches
    segment = mi_segment_cache_find(tld,segment_size); 

    // and otherwise allocate it from the OS
    if (segment == NULL) {
        segment = (mi_segment_t*)_mi_os_alloc_aligned(segment_size, MI_SEGMENT_SIZE, os_tld);
        if (segment == NULL) return NULL;
        mi_segments_track_size((long)segment_size,tld);
    }

    memset(segment, 0, info_size);
    segment->page_kind  = page_kind;
    segment->capacity   = capacity;
    segment->page_shift = page_shift;
    segment->segment_size = segment_size;
    segment->segment_info_size = pre_size;
    segment->thread_id  = _mi_thread_id();
    for (uint8_t i = 0; i < segment->capacity; i++) segment->pages[i].segment_idx = i;
    return segment;
    ```
    * `capacity = (4194304, 4Mib) / page_size (1 << (page_shift = 16) = 65536, 64Kib) = 64`
    * `mi_segment_size` calculates the real segment size and also incorporates the metadata
        roughly: `size_t minsize   = sizeof(mi_segment_t) + ((capacity - 1) * sizeof(mi_page_t)) + 16 /* padding */;`
        it sets `info_size` to TODO(Ben): ?
        it set `pre_size` to TODO(Benn): ?
    * TODO(Ben): skipping the cache stuff for now (`mi_segment_cache_find(tdl,segment_size)`)
    * Most notable line: `segment = (mi_segment_t*)_mi_os_alloc_aligned(segment_size, MI_SEGMENT_SIZE, os_tld);`
        so we call `_mi_os_alloc_aligned` with a 4Mib alignment 
 
- Go to Step 13: `_mi_os_alloc_aligned(segment_size, MI_SEGMENT_SIZE, os_tld);`

> Returned form Step 13: `_mi_os_alloc_aligned(segment_size, MI_SEGMENT_SIZE, os_tld);`
    some initialisatoin stuff, nothing major

---

## Step 13: `_mi_os_alloc_aligned(segment_size, MI_SEGMENT_SIZE, os_tld);`
- At os.c:~312
    ```
    void* _mi_os_alloc_aligned(size_t size, size_t alignment, mi_os_tld_t* tld) {...}
    ```
    allocate an aligned block of virtual memory.
    Since `mi_mmap` is relatively slow we try to allocate directly at first and
    hope to get an aligned address; only when that fails we fall back
    to a guaranteed method by overallocating at first and adjusting.

- Important code
    ```
    if (alignment < 1024) return _mi_os_alloc(size, tld->stats);

    void* p = os_pool_alloc(size,alignment,tld);
    if (p != NULL) return p;

    void* suggest = NULL;

    if (p==NULL && (tld->mmap_next_probable % alignment) == 0) {
        // if the next probable address is aligned,
        // then try to just allocate `size` and hope it is aligned...
        p = mi_mmap(suggest, size, 0, tld->stats);
        if (p == NULL) return NULL;
        if (((uintptr_t)p % alignment) == 0) mi_stat_increase(tld->stats->mmap_right_align, 1);
    }
    ```
    * since alignment for segments is huge we actually done't call `_mi_os_alloc`
    * so we call `so_pool_alloc in os.c:368`
    * we actually fail that call, since we haven't set the pool-commit flag 
    * I think this is because there is a high probablility of failing the huge alignment this way?
    * mmap's only guarentees hints about input address, but no idea of that is actually the reason
    * so we get to the `mi_mmap` in the if statement 

- Go to Step 14: `mi_mmap(suggets, size, 0, tld->stats)` 

> Returned from Step 15: 
    * we return after mmap hopefully succesfully
    * now we still check alignment we wanted may 
    * do slower gaurenteed way

---

## Step 14: `mi_mmap(suggets, size, 0, tld->stats)` 
- At os.c:~99
    ```
    static void* mi_mmap(void* addr, size_t size, int extra_flags, mi_stats_t* stats) {...}
    ```

- Important code 
    This is bascially the linux verion of that function
    ```
    void* p;
    int flags = MAP_PRIVATE | MAP_ANONYMOUS | extra_flags;
    int pflags = PROT_READ | PROT_WRITE;
    p = mmap(addr, size, pflags, flags, -1, 0);
    if (p == MAP_FAILED) p = NULL;
    if (addr != NULL && p != addr) {
        mi_munmap(p, size);
        p = NULL;
    }
    return p;
    }
    ```
    * TODO(Ben): how dies this align it, it uses suggest for that but it is not guarenteed
    * `flags = MAP_PRIVATE | MAP_ANONYMOUS | extra_flags = 0;`
    * `MAP_PRIVATE` means only for this process,
    * `MAP_ANONYMOUS` anonymous means copy-on-write not backed by memory
    * read-write memory for pflags
