#include "simplemimalloc.c"

#define container_of(ptr, member, type) \
   (type *)((u8*)ptr - offsetof(type, member))

typedef struct IListNode {
    struct IListNode *next;
} IListNode;

typedef struct {
    IListNode head; 
    IListNode tail;
} FreeQueue;

//dummy object
typedef struct Object {
    IListNode node;
    struct Object *child1;
    struct Object *child2;
} Object;

internal bool done_freeing = false;

//FreeQueue functions 
void fq_push_back (FreeQueue *queue, IListNode *node) {
    node->next = NULL; 
    if (!queue->tail.next) {
        queue->head.next = node; 
        queue->tail.next = node;
    } else {
        queue->tail.next->next = node;
        queue->tail.next = node;
    }
}

IListNode *fq_pop_front (FreeQueue *queue) {
    if (!queue->head.next) return NULL;

    IListNode *first = queue->head.next;
    queue->head.next = first->next;

    if (!queue->head.next) queue->tail.next = NULL;

    first->next = NULL;
    return first;
}

bool fq_empty (FreeQueue *queue) {
    return !queue->head.next;
}

//runtime functions
bool make_pointer_tree_rec (Object *now, i32 depth) {
    if (depth == 0) return true;
    now = sm_malloc(sizeof(Object));
    memset(now, 0, sizeof(Object));
    if (!now) return false;
    make_pointer_tree_rec(now->child1, depth - 1);
    make_pointer_tree_rec(now->child2, depth - 1);
}

//depth = 18, exactly 4 Mib
void *make_pointer_tree (i32 depth) {
    Object *root = NULL;
    if (!make_pointer_tree_rec (root, depth)) return NULL;
    return root;
}

//very lazy fully relies on deferred freeing
void runtime_free (FreeQueue *free_queue, Object *obj) {
    fq_push_back(free_queue, &obj->node); 
}

void deferred_callback (bool force, unsigned long long heartbeat, void *arg);

void runtime () {
    FreeQueue free_queue = {0};
    sm_register_deferred_free(deferred_callback, &free_queue); 

    Object *obj = make_pointer_tree(18);
    if (!obj) return;
    
    while (!done_freeing) {
        //(simple-)mimalloc should guarentee that this is sufficient for calling deferred_callback regularly
        Object *obj = sm_malloc(sizeof(Object));
        runtime_free(&free_queue, obj);
    }
}

//allocator callback
void deferred_callback (bool force, unsigned long long heartbeat, void *arg) {
    if (!arg) return;
    FreeQueue *free_queue = (FreeQueue*)arg;

    i32 max_free = 100;
    i32 i = 0;

    while (i < max_free) {
        if (fq_empty(free_queue)) break;
        Object *now = container_of(fq_pop_front(free_queue), node, Object);
        if (now->child1) fq_push_back(free_queue, &now->child1->node); 
        if (now->child2) fq_push_back(free_queue, &now->child2->node);
        i++;
    }

    if (fq_empty(free_queue)) done_freeing = true; 
}

//test
i32 main () {
    SMDEBUG("----------TEST 1-----------\n")
    runtime();
    SMDEBUG("Succeeded in clearing pointer tree\n")
    SMDEBUG("--------------------------\n")
    return 0;
}
