/*
 * mm_version3.0 显式空闲链表 + LIFO + 分离适配组织空闲链表 + 首次适配的匹配策略
 */
#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <unistd.h>
#include <string.h>

#include "mm.h"
#include "memlib.h"

#define MY_DEBUG 0
#define MY_CHECK 0
#define MY_PRINT 0
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

/* 4K， 要求为页面大小的整数倍 */
#define CHUNKSIZE   (1 << 12) 
/* 分离链表的空间分别为 |(16-31)|(32-63)|(64-127)|(128-255)| ..... |(2^23,正无穷)| */
/* 这个数字可调来找到最大得分 */
#define MAX_EMPTY_LISTS     20 // 分离链表最大数量
/* 为了能存储 hdr pred succ ftr 最少需要 16B */
#define MIN_BLOCK_SIZE      16 // 最小块的大小

void* heap_listp = 0;
void* list_root[MAX_EMPTY_LISTS] = {0}; // 作为空闲链表的头结点数组

static void *extend_heap(size_t words);
static void *coalesce(void *bp);
static void *find_fit(size_t size);
static void place(void *bp, size_t asize);
static void add_to_empty_list(void *bp);
static void delete_from_empty_list(void *bp);
static void mm_check(void);
static void block_in_empty_list(void *bp);
static void print_empty_list(char *s);

/* 
 * mm_init - initialize the malloc package.
 */
int mm_init(void)
{
    /* 给隐式链表的头部和尾部分配空间 */  
    if ((heap_listp = mem_sbrk((4 + 2*MAX_EMPTY_LISTS) * WSIZE)) == (void*)-1)
        return -1;
    
    /* 初始格式是 | 0 | free list roots | 序言块 | 结尾块 | */
    /* 空间      | 1 |2*MAX_EMPTY_LISTS|   2   |   1   | WSIZE */
    PUT(heap_listp, 0);
    for (int i = 0; i < MAX_EMPTY_LISTS; i++) {
        PUT(heap_listp + ((2*i + 1)*WSIZE), NULL); // root
        PUT(heap_listp + ((2*i + 2)*WSIZE), NULL); // 对应位置存的是一个地址，所以设为NULL
    }
    PUT(heap_listp + ((2*MAX_EMPTY_LISTS + 1)*WSIZE), PACK(DSIZE, 1)); // 序言块
    PUT(heap_listp + ((2*MAX_EMPTY_LISTS + 2)*WSIZE), PACK(DSIZE, 1)); // 序言块
    PUT(heap_listp + ((2*MAX_EMPTY_LISTS + 3)*WSIZE), PACK(0, 1)); // 结尾块

    /* 初始化 list_root */
    for (int i = 0; i < MAX_EMPTY_LISTS; i++) {
        list_root[i] = heap_listp + (2*i + 1) * WSIZE;
    }
    heap_listp += (2 + 2*MAX_EMPTY_LISTS) * WSIZE;
    
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
    
    if (MY_CHECK)
        mm_check();

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

    if (MY_CHECK)
        mm_check();

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

    if (MY_CHECK)
        mm_check();
}

/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 * 后面可看看怎么不依赖前面的函数实现
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
    /* 如果realloc asize < old size, 直接返回原ptr */
    size_t old_size = GET_SIZE(HDRP(ptr));
    if (asize <= old_size) {
        return ptr;
    }

    /* 
        如后一个块未分配且大小合适，可直接合并后返回
        虽然这样可能会造成一些不必要的内部碎片，但在实验测例中效果明显
     */
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(ptr)));
    size_t next_size = GET_SIZE(HDRP(NEXT_BLKP(ptr)));
    if (!next_alloc && (asize <= next_size + old_size)) {
        /* 将下一个块在空闲链表中的前驱后继维护好 */
        delete_from_empty_list(NEXT_BLKP(ptr));

        PUT(HDRP(ptr), PACK(next_size+old_size, 1));
        /* 使用 FTBR 宏时，需要通过hdr 得到size, 然后找到 ftr 进行设置 */
        PUT(FTRP(ptr), PACK(next_size+old_size,1));     

        return ptr;
    }

    if (MY_DEBUG)
        printf("remalloc: size = %u, asize = %u\n", size, asize);
/*
 * 下面三个函数的调用顺序需要注意：
 *      必须先malloc再free, 否则原来 block 中的content可能会被 footer和pred,succ等破坏
 *      同理，需要先 memcpy 再 free, 因为free时会在空闲块负载部分加上 pred, succ
 */
    void *new_ptr = mm_malloc(asize);
    memcpy(new_ptr, ptr, old_size);
    mm_free(ptr);

    if (MY_CHECK)
        mm_check();

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

    /* 需要先将本空闲块从空闲链表中移除 */
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

    int index = -1;
    /* 首先找到需要从哪个空闲链表中进行搜寻*/
    for (int i = 0; i < MAX_EMPTY_LISTS - 1; i++) {
        /* 注意第 i 个空闲链表适合于 size [2^(i+4), 2^(i+5)), 第 0 个空闲链表除外 */
        if ( size < (1 << (i + 5)) ) {
            index = i;
            break;
        }
    }
    // 若此时没有合适的块，在最后一个链表中搜索
    index = (index >= 0) ? index : MAX_EMPTY_LISTS-1;

    /* 说明能找到适合大小的空闲链表 */
    while (index < MAX_EMPTY_LISTS) {
        for (void *bp = SUCC_BLKP(list_root[index]); bp != NULL; bp = SUCC_BLKP(bp)) {
            /* 找到足够大而且未分配的块 */
            if (GET_SIZE(HDRP(bp)) >= size) 
                return bp;  
        }
        /* 说明之前空闲链表内找不到合适的空闲块，对更大的空闲块链表搜索 */
        index++;
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
    if (avail_size < asize + MIN_BLOCK_SIZE ) {
        PUT(HDRP(bp), PACK(avail_size, 1));
        PUT(FTRP(bp), PACK(avail_size, 1));

        return;
    }

    /* 剩余部分大于最小块，需要设置剩余块 */ 
    PUT(HDRP(bp), PACK(asize, 1));
    /* 因为 FTRP 是根据 hdr中的size来确定的，所以可直接调用 */
    PUT(FTRP(bp), PACK(asize, 1));
    PUT(HDRP(NEXT_BLKP(bp)), PACK(left_size, 0));
    PUT(FTRP(NEXT_BLKP(bp)), PACK(left_size, 0));

    /* 将剩余的空闲块插入空闲链表 */ 
    add_to_empty_list(NEXT_BLKP(bp));
}

/* 按照 后进先出 的顺序维护空闲链表 */
static void add_to_empty_list(void *bp) {
    size_t size = GET_SIZE(HDRP(bp));
    int index = -1;

    /* 首先找到向哪个链表插入*/
    for (int i = 0; i < MAX_EMPTY_LISTS - 1; i++) {
        if ( size < (1 << (i + 5)) ) {
            index = i;
            break;
        }
    }

    // 若此时没有合适的空闲块链，直接插入最后一个链表
    index = index >= 0 ? index : MAX_EMPTY_LISTS-1;

    void *root_succ = SUCC_BLKP(list_root[index]);
    /* bp->pred = root */
    PUT(PRED(bp), list_root[index]);
    /* bp->succ = address(root->succ) */
    PUT(SUCC(bp), SUCC_BLKP(list_root[index]));
    /* (bp->succ)->pred = bp, 若当前空闲链表非空，需要设置root的后继节点的前驱结点*/
    if (root_succ != NULL)
        PUT(PRED(SUCC_BLKP(list_root[index])), bp);
    /* root->succ = bp */
    PUT(SUCC(list_root[index]), bp);

    if (MY_PRINT)
        print_empty_list("called by add_to_empty_list");
}

/* 从空闲链表中删除对应空闲块并维护好链表的前驱后继关系 */
static void delete_from_empty_list(void *bp) {
    /* bp->pred->succ = address(bp->succ) */
    PUT(SUCC(PRED_BLKP(bp)), SUCC_BLKP(bp));
    /* bp->succ->pred = address(bp->pred) */
    if (SUCC_BLKP(bp) != NULL) /* 考虑特殊情况，若当前块的后继为空，上面描述的关系无需维护 */ 
        PUT(PRED(SUCC_BLKP(bp)), PRED_BLKP(bp));

    if (MY_PRINT) 
        print_empty_list("called by delete_from_empty_list");
}

/* 依次实现各检查项 */
static void mm_check(void) {
    void *bp = NULL;

    for (int i = 0; i < MAX_EMPTY_LISTS; i++) {
        for (bp = SUCC_BLKP(list_root[i]); bp != NULL; bp = SUCC_BLKP(bp)) {
            if (bp == PRED_BLKP(bp)) {
                printf("error\n");
                exit(1);
            }

            /* 1. check every block in the free list marked as free */
            if (GET_ALLOC(HDRP(bp)) || GET_ALLOC(FTRP(bp))) {
                printf("error: the block in the free list is not free.\n");
                exit(1);
            }
            // printf("mm_check: bp = %p, pred bp = 0x%x, succ bp = 0x%x\n", bp, PRED_BLKP(bp), SUCC_BLKP(bp));    

            /* 2. there any contiguous free blocks that somehow escaped coalescing? */
            if (!GET_ALLOC(HDRP(PREV_BLKP(bp))) || !GET_ALLOC(HDRP(NEXT_BLKP(bp)))) {
                printf("error: there are any contiguous free blocks that somehow escaped coalescing.\n");
                exit(1);
            }

        }
    }

    for (bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)) {
        if (GET_ALLOC(HDRP(bp)) != GET_ALLOC(FTRP(bp))) {
            printf("error: bp = %p, block hdr != ftr.\n", bp);
            if (PREV_BLKP(bp))
                printf("prev bp = 0x%x, size = %u. ", PREV_BLKP(bp), GET_SIZE(PREV_BLKP(bp)));
            if (NEXT_BLKP(bp))
                printf("next bp = 0x%x, size = %u \033[0m\n", NEXT_BLKP(bp),GET_SIZE(NEXT_BLKP(bp)));
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
    size_t size = GET_SIZE(HDRP(ptr));
    int index = -1;

    /* 首先找到需要从哪个空闲链表中进行搜寻*/
    for (int i = 0; i < MAX_EMPTY_LISTS - 1; i++) {
        if ( size < (1 << (i + 5)) ) {
            index = i;
            break;
        }
    }

    // 若此时没有合适的块，在最后一个链表中搜索
    index = index >= 0 ? index : MAX_EMPTY_LISTS-1;

    for (void *bp = SUCC_BLKP(list_root[index]); bp != NULL; bp = SUCC_BLKP(bp)) {
        if (bp == ptr) 
            return;
    }


    printf("error: not every free block actually in the free list.\n");
    exit(1);
}

static void print_empty_list(char *s) {
    printf("\n%s", s);
    printf("\n\033[31m==========Empty List Start=========\033[0m\n");
    for (int i = 0; i < MAX_EMPTY_LISTS; i++) {
        printf("\033[32m----------empty list %d start-------------\033[0m\n", i);

        for (void *bp = SUCC_BLKP(list_root[i]) ; bp ; bp = SUCC_BLKP(bp)) {
            printf("\033[32m size = %u, bp = %p ", GET_SIZE(HDRP(bp)), bp); 
            if (PRED_BLKP(bp))
                printf("pred bp = 0x%x ", PRED_BLKP(bp));
            if (SUCC_BLKP(bp))
                printf("succ bp = 0x%x\033[0m\n", SUCC_BLKP(bp));
        }

        printf("\n\033[32m----------empty list %d end-------------\033[0m\n", i);
    }


    printf("\n\033[31m==========Empty List End=========\033[0m\n");
}