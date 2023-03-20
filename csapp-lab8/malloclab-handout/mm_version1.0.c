/*
 * mm_version1.0 显示空闲链表+LIFO
 */
#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <unistd.h>
#include <string.h>

#include "mm.h"
#include "memlib.h"

#define MY_DEBUG 0
/*********************************************************
 * NOTE TO STUDENTS: Before you do anything else, please
 * provide your team information in the following struct.
 ********************************************************/
team_t team = {
    /* Team name */
    "ateam",
    /* First member's full name */
    "Harry Bovik",
    /* First member's email address */
    "bovik@cs.cmu.edu",
    /* Second member's full name (leave blank if none) */
    "",
    /* Second member's email address (leave blank if none) */
    ""
};

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~0x7)


#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

/* from textbook 9.9.12 */
#define WSIZE       4
#define DSIZE       8
#define CHUNKSIZE   (1 << 12) // 4K

#define MAX(x, y)   ((x) > (y) ? x : y)
#define MIN(x, y)   ((x) > (y) ? y : x)

#define PACK(size, alloc) ((size) | (alloc))

#define GET(p)      (*(unsigned int *)(p))
#define PUT(p, val) (*(unsigned int *)(p) = (val))

#define GET_SIZE(p) (GET(p) & ~0x7)
#define GET_ALLOC(p) (GET(p) & 0x1)

#define HDRP(bp)    ((char *)(bp) - WSIZE)
#define FTRP(bp)    ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))
#define PREV_BLKP(bp) ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))

#define PRED(bp)    ((char *)(bp)) // 存储祖先节点地址的地址
#define SUCC(bp)    ((char *)(bp) + WSIZE) // 存储后继节点地址的地址

#define PRED_BLKP(bp) GET(PRED(bp)) // 祖先节点的地址
#define SUCC_BLKP(bp) GET(SUCC(bp)) // 后继节点的地址

void* heap_listp = 0;
void* root = 0; // 作为空闲链表的头结点

static void *extend_heap(size_t words);
static void *coalesce(void *bp);
static void *find_fit(size_t size);
static void place(void *bp, size_t asize);
static void add_to_empty_list(void *bp);
static void delete_from_empty_list(void *bp);
static void mm_check(void);
static void block_in_empty_list(void *bp);
static void print_empty_list(void);

/* 
 * mm_init - initialize the malloc package.
 */
int mm_init(void)
{
    /* 给隐式链表的头部和尾部分配空间 */  
    if ((heap_listp = mem_sbrk(6 * WSIZE)) == (void*)-1)
        return -1;
    
    PUT(heap_listp, 0);
    PUT(heap_listp + (1*WSIZE), PACK(2*DSIZE, 1)); // 序言块
    PUT(heap_listp + (2*WSIZE), NULL); // root
    PUT(heap_listp + (3*WSIZE), NULL); // 对应位置存的是一个地址，所以设为NULL
    PUT(heap_listp + (4*WSIZE), PACK(2*DSIZE, 1)); // 序言块
    PUT(heap_listp + (5*WSIZE), PACK(0, 1)); // 结尾块

    /* 初始化 root */
    root = heap_listp + (2 * WSIZE);
    heap_listp += (2 * WSIZE);
    
    if (extend_heap(CHUNKSIZE/WSIZE) == NULL)
        return -1;

    return 0;
}

/* 
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 */
void *mm_malloc(size_t size)
{
    size_t extendsize;
    size_t asize = ALIGN(size + SIZE_T_SIZE);
    char *bp;
    if (MY_DEBUG)
        printf("malloc: size = %u , asize = %u \n", size, asize);

    if (size == 0)
        return NULL;
    
    //mm_check();

    /* Search the free list for a fit */
    if ((bp = find_fit(asize)) != NULL) {
        place(bp, asize);

        return bp;
    }

    /* No fit found. Get more memory and place the block */
    extendsize = MAX(asize, CHUNKSIZE);
    if ((bp = extend_heap(extendsize/WSIZE)) == NULL)
        return NULL;
    place(bp, asize);

    //mm_check();

    return bp;
}

/*
 * mm_free - Freeing a block does nothing.
 */
void mm_free(void *ptr)
{
    if (ptr == NULL)
        return;

    size_t size = GET_SIZE(HDRP(ptr));
    if (MY_DEBUG)
        printf("free: size = %u \n", size);

    PUT(HDRP(ptr), PACK(size, 0)); // 设置未分配
    PUT(FTRP(ptr), PACK(size, 0));
    
    add_to_empty_list(ptr);

    coalesce(ptr);

    //mm_check();
}

/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 */
void *mm_realloc(void *ptr, size_t size)
{
    if (ptr == NULL)
        return mm_malloc(size);
    
    if (size == 0) {
        mm_free(ptr);
        return NULL;
    }
    size_t asize = ALIGN(size + SIZE_T_SIZE);

    if (MY_DEBUG)
        printf("malloc: size = %u , asize = %u \n", size, asize);

    if (size == asize) {
        return ptr;
    }

/*
 * 下面三个函数的调用顺序需要注意：
 *      必须先malloc再free, 否则原来 block 中的content可能会被 footer和pred,succ等破坏
 *      同理，需要先 memcpy 再 free.
 */
    void *new_ptr = mm_malloc(asize);
    memcpy(new_ptr, ptr, MIN(asize, size));
    mm_free(ptr);

    //mm_check();

    return new_ptr;
}

/*  扩展堆空间，并设置对应的 hdr, ftr */
static void *extend_heap(size_t words) {
    char *bp;
    size_t size;

    // 8B 对齐
    size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE;

    if (MY_DEBUG)
        printf("extend heap: size = %u \n", size);
    if ((long)(bp = mem_sbrk(size)) == -1) 
        return NULL;

    /* 设置 hdr */
    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1)); // 设置结尾块

    /* 加入空闲块链表 */
    add_to_empty_list(bp);

    /* 合并空闲块 */
    return coalesce(bp);
}

/* 合并前后块并返回合并后的 bp */
static void *coalesce(void *bp) {
    /* 通过前一个块的 ftr 判断前一个块是否分配 */
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    /* 通过后一个块的 hdr 判断后一个块是否分配 */
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));

    /* 讨论以下四种情况 */
    if (prev_alloc && next_alloc) {
        return bp;
    }

    /* 需要先将本空闲块从空闲链表中移除。这一点忽略了，找了半天bug，呜呜呜 */
    delete_from_empty_list(bp);

    if (prev_alloc && !next_alloc) {
        /* 将下一个块在空闲链表中的前驱后继维护好 */
        delete_from_empty_list(NEXT_BLKP(bp));

        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(bp), PACK(size, 0));
        /* 使用 FTBR 宏时，需要通过hdr 得到size, 然后找到 ftr 进行设置 */
        PUT(FTRP(bp), PACK(size,0)); 
    }
    else if (!prev_alloc && next_alloc) {
        delete_from_empty_list(PREV_BLKP(bp));

        size += GET_SIZE(FTRP(PREV_BLKP(bp)));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));

        bp = PREV_BLKP(bp);
    }
    else {
        delete_from_empty_list(PREV_BLKP(bp));
        delete_from_empty_list(NEXT_BLKP(bp));

        size += GET_SIZE(HDRP(NEXT_BLKP(bp))) + GET_SIZE(FTRP(PREV_BLKP(bp)));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));

        bp = PREV_BLKP(bp);
    }

    /* 将合并好的空闲加入空闲链表的头 */
    add_to_empty_list(bp);

    return bp;
}

/* 从空闲链表中首次适配搜索,返回首次适配的块的 bp */
static void *find_fit(size_t size) {
    if (MY_DEBUG)
        printf("enter find_fit\n");

    for (void *bp = SUCC_BLKP(root); bp != NULL; bp = SUCC_BLKP(bp)) {
        //printf("Find fit: size = %u, block_size = %u\n", size, block_size);
        /* 找到足够大而且未分配的块 */
        if (GET_SIZE(HDRP(bp)) >= size) 
            return bp;  
    }

    if (MY_DEBUG)
        printf("Couldn't find fit. \n");

    return NULL;
}

/* 将请求块放置在空闲块的起始位置，只有当剩余部分大小 >= 最小块大小时，才进行分割 */
static void place(void *bp, size_t asize) {
    size_t avail_size = GET_SIZE(HDRP(bp));
    size_t left_size = avail_size - asize;

    /* 首先从空闲链表中删除待分配块 */ 
    delete_from_empty_list(bp);

    /*
        若剩余部分小于最小块，将整个块全部分配
        由于显示空闲链表需要存储前驱后继的地址，最小块要求更大
    */
    if (GET_SIZE(HDRP(bp)) <= asize + 2*SIZE_T_SIZE ) {
        PUT(HDRP(bp), PACK(avail_size, 1));
        PUT(FTRP(bp), PACK(avail_size, 1));

        return;
    }

    /*
        剩余部分大于最小块，需要设置剩余块
        设置已分配的块
    */ 
    PUT(HDRP(bp), PACK(asize, 1));
    // 因为 FTRP 是根据 hdr中的size来确定的，所以可直接调用
    PUT(FTRP(bp), PACK(asize, 1));
    PUT(HDRP(NEXT_BLKP(bp)), PACK(left_size, 0));
    PUT(FTRP(NEXT_BLKP(bp)), PACK(left_size, 0));

    /* 将剩余的空闲块插入空闲链表 */ 
    add_to_empty_list(NEXT_BLKP(bp));
}

/* 使用后进先出的策略管理空闲链表，新释放/分配的空闲块放在链表开头 */
static void add_to_empty_list(void *bp) {
    void *root_succ = SUCC_BLKP(root);

    /* bp->pred = root */
    PUT(PRED(bp), root);
    /* bp->succ = address(root->succ) */
    PUT(SUCC(bp), SUCC_BLKP(root));
    /* (bp->succ)->pred = bp, 若当前空闲链表非空，需要设置root的后继节点的前驱结点*/
    if (root_succ != NULL)
        PUT(PRED(SUCC_BLKP(root)), bp);
    /* root->succ = bp */
    PUT(SUCC(root), bp);

    //print_empty_list();
}

/* 从空闲链表中删除对应空闲块并维护好链表的前驱后继关系 */
static void delete_from_empty_list(void *bp) {
    /* bp->pred->succ = address(bp->succ) */
    PUT(SUCC(PRED_BLKP(bp)), SUCC_BLKP(bp));
    /* bp->succ->pred = address(bp->pred) */
    if (SUCC_BLKP(bp) != NULL) /* 考虑特殊情况，若当前块的后继为空，上面描述的关系无需维护 */ 
        PUT(PRED(SUCC_BLKP(bp)), PRED_BLKP(bp));

    //print_empty_list();
}

/* 依次实现各检查项 */
static void mm_check(void) {
    void *bp = NULL;

    for (bp = SUCC_BLKP(root); bp != NULL; bp = SUCC_BLKP(bp)) {
        if (bp == PRED_BLKP(bp)) {
            printf("error\n");
            exit(1);
        }

        /* 1. check every block in the free list marked as free */
        if (GET_ALLOC(HDRP(bp)) || GET_ALLOC(FTRP(bp))) {
            printf("error: the block in the free list is not free.\n");
            exit(1);
        }
        printf("mm_check: bp = %p, pred bp = 0x%x, succ bp = 0x%x\n", bp, PRED_BLKP(bp), SUCC_BLKP(bp));    

        /* 2. there any contiguous free blocks that somehow escaped coalescing? */
        if (!GET_ALLOC(HDRP(PREV_BLKP(bp))) || !GET_ALLOC(HDRP(NEXT_BLKP(bp)))) {
            printf("error: there are any contiguous free blocks that somehow escaped coalescing.\n");
            exit(1);
        }

    }

    for (bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)) {
        if (GET_ALLOC(HDRP(bp)) != GET_ALLOC(FTRP(bp))) {
            printf("error: block hdr != ftr.\n");
            exit(1);
        }

        /* 3. Is every free block actually in the free list */
        if (!GET_ALLOC(HDRP(bp)) || !GET_ALLOC(FTRP(bp))) {
            block_in_empty_list(bp);
        }

        /* 4. Do the pointers in the free list point to valid free blocks */

        /* 5. Do any allocated blocks overlap */

        /* 6. Do the pointers in a heap block point to valid heap addresses */
    }
}

static void block_in_empty_list(void *ptr) {
    for (void *bp = SUCC_BLKP(root); bp != NULL; bp = SUCC_BLKP(bp)) {
        if (bp == ptr) 
            return;
    }

    printf("error: not every free block actually in the free list.\n");
    exit(1);
}

static void print_empty_list(void) {
    printf("\n\033[31m==========Empty List Start=========\033[0m\n");
    void *bp = SUCC_BLKP(root);
    for (  ; bp ; bp = SUCC_BLKP(bp)) {
        printf("\033[32m size = %u, bp = %p ", GET_SIZE(HDRP(bp)), bp); 
        if (PRED_BLKP(bp))
            printf("pred bp = 0x%x ", PRED_BLKP(bp));
        if (SUCC_BLKP(bp))
            printf("succ bp = 0x%x\033[0m\n", SUCC_BLKP(bp));
    }


    printf("\n\033[31m==========Empty List End=========\033[0m\n");
}