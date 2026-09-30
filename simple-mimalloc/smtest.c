#include "simplemimalloc.c"

void sm_reset () {
    sm_segment_t *segment = global_heap.first;
    while (segment) {
        sm_segment_t *temp = segment->next;
        sm_munmap(segment, SM_PAGE_SIZE * SM_N_PAGES_PER_SEGMENT);
        segment = temp;
    }
    memset(&global_heap, 0, sizeof(sm_heap_t));
}

/* Test 1: allocate and free 
    all the way slow path: os allocate first segment
*/
void test1 () {
    SMDEBUG("----------TEST 1-----------\n")
    void *data = sm_malloc(500);  
    sm_free(data);
    SMDEBUG("--------------------------\n")
}

/* Test 2: allocate and free multiple times 
    should always return the same block
    since it should collect free blocks first: (page->free = page->local_free)
    only after that it page extends: which should not be hit.
*/
void test2 () {
    SMDEBUG("----------TEST 2-----------\n")
    int enough = SM_SEGMENT_SIZE / SM_PAGE_SIZE;
    void *data = sm_malloc(500);
    sm_free(data);
    void *prev = data; 
    for (int i = 0; i < enough; i++) {
        data = sm_malloc(500);
        SMASSERT(prev == data)
        prev = data;
        sm_free(data);
    }
    SMDEBUG("--------------------------\n")
}
/* Test 3: allocate enough to page extend multiple times  
    it should extend 4 times: 1 -> 2, 2 -> 4, 4 -> 8, 8 -> 16 
*/ 
void test3 () {
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
}

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
void test4 () {
    SMDEBUG("----------TEST 4-----------\n")
    void *datas[64];
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
}

/* Test 5: allocate in different size classes 
    allocate x1 <= 512 and 512 < x2 <= 1024 
    then we should get that two page queues have a page
*/
void test5 () {
    SMDEBUG("----------TEST 5-----------\n")
    void *data = sm_malloc(500); 
    void *data2 = sm_malloc(1000);
    sm_free(data);
    sm_free(data2);
    SMASSERT(global_heap.page_qs[sm_bin(500)].first && global_heap.page_qs[sm_bin(1000)].first)
    SMDEBUG("--------------------------\n")
}

i32 main () {
    test1();
    sm_reset();
    test2();
    sm_reset();
    test3();
    //sm_reset();
    //test4(); //TODO(Ben): tests fails as if now
    sm_reset();
    test5();
    return 0;
}
