/*
 * mm-naive.c - 一个非常快，但内存效率低的 malloc 包。
 *
 * 在这个简单的方法中，通过简单地增加 brk 指针来分配块。
 * 块从未被合并或重用。块的大小存储在块头中，因为 realloc 需要它。
 *
 * 
 * 
 * 
 * 这个代码是正确且快速的，但在某些情况下会失败，并且利用率很差。
 */

#include <assert.h>
#include <inttypes.h>
#include <stdbool.h>
#include <stddef.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

#include "memlib.h"
#include "mm.h"

/* 不要更改以下内容！ */

#ifdef DRIVER
/* 为 driver 测试创建别名 */
#define malloc mm_malloc
#define free mm_free
#define realloc mm_realloc
#define calloc mm_calloc
#define memset mem_memset
#define memcpy mem_memcpy
#endif /* def DRIVER */

/* 你可以从此处开始更改任何内容 */

/*
 * 如果定义了 DEBUG（例如在运行 mdriver-dbg 时），这些宏将被启用。

 * 你可以在调试模式下使用它们来打印调试输出和检查合约。
 *
 * 仅允许以 "dbg_" 开头的调试宏。你不能定义任何带有参数的其他宏。
 * 
 */
#ifdef DEBUG
/* 当定义了 DEBUG 时，这些形成有用函数的别名 */
#define dbg_printf(...) ((void)printf(__VA_ARGS__))
#define dbg_requires(expr) assert(expr)
#define dbg_assert(expr) assert(expr)
#define dbg_ensures(expr) assert(expr)
#define dbg_printheap(...) print_heap(__VA_ARGS__)
#else
/* 当未定义 DEBUG 时，不会生成这些代码 */
/* 使用 sizeof() 技巧来避免 "未使用变量" 警告 */
#define dbg_printf(...) ((void)sizeof(printf(__VA_ARGS__)))
#define dbg_requires(expr) ((void)sizeof(expr))
#define dbg_assert(expr) ((void)sizeof(expr))
#define dbg_ensures(expr) ((void)sizeof(expr))
#define dbg_printheap(...) ((void)sizeof(print_heap(__VA_ARGS__)))
#endif

typedef uint64_t word_t;
#define WSIZE sizeof(word_t)

/* 正确的对齐方式是什么？ */
#define ALIGNMENT (2 * WSIZE)

/*
 * 将内存视为块组织，块头表示块大小，负载包含实际数据

 */
typedef struct {
    word_t size;     // 分配的总大小
    word_t padding;  // 确保负载对齐
    char payload[0]; // 负载大小是可变的
} block_t;

/*
 * 从负载到块头的偏移量是多少？
 */
#define HEADER_SIZE offsetof(block_t, payload)

/*
 * 支持函数的前向声明
 */
static block_t *payload_to_header(void *bp);
static void *header_to_payload(block_t *block);
static size_t roundup(size_t size, size_t multiple);

/*
 * mm_init - 在一个新的 trace 开始时调用。
 * 注意：你必须在这里重置所有全局指针。
 */
bool mm_init(void) {
    return true;
}

/*
 * malloc - 通过扩展堆分配一个块
 */
void *malloc(size_t size) {
    size_t newsize = roundup(size + HEADER_SIZE, ALIGNMENT);
    block_t *block = (block_t *)mem_sbrk((intptr_t)newsize);

    if (block == (void *)-1)
        return NULL;
    else {
        block->size = newsize;
        void *p = header_to_payload(block);
        dbg_printf("malloc %zu => %p\n", size, p);
        return p;
    }
}

/*
 * free - 我们不知道如何释放一个块。所以我们忽略这个调用。
 * 计算机有大内存；肯定不会有问题。
 */
void free(void *ptr) {
    dbg_printf("free(%p)\n", ptr);
}

/*
 * realloc - 通过分配一个新块，复制数据并释放旧块来更改块的大小。

 * 我太懒了，不想做得更好。
 */
void *realloc(void *oldptr, size_t size) {
    /* 如果 size == 0，则这只是 free，我们返回 NULL。 */
    if (size == 0) {
        free(oldptr);
        return NULL;
    }

    /* 如果 oldptr 是 NULL，则这只是 malloc。 */
    if (oldptr == NULL) {
        return malloc(size);
    }

    void *newptr = malloc(size);

    /* 如果 realloc() 失败，原始块保持不变 */
    if (!newptr) {
        return NULL;
    }

    /* 复制旧数据。 */
    block_t *block = payload_to_header(oldptr);
    size_t copysize = block->size;
    if (size < copysize)
        copysize = size;
    memcpy(newptr, oldptr, copysize);

    /* 释放旧块。 */
    free(oldptr);

    return newptr;
}

/*
 * calloc - 分配块并将其置零。
 */
void *calloc(size_t nmemb, size_t size) {
    size_t bytes = nmemb * size;
    void *newptr;

    newptr = malloc(bytes);
    memset(newptr, 0, bytes);

    return newptr;
}

/*
 * mm_checkheap - 我的代码中没有错误，所以我不需要检查，所以不检查！
 * （但如果我确实需要，我可以使用 mm_checkheap(__LINE__) 调用这个函数来标识调用位置。）
 */
bool mm_checkheap(int lineno) {
    dbg_printf("Checkheap called at line %d\n", lineno);
    return true;
}

/***********************************************************************
 * 支持函数
 ***********************************************************************/

/* payload -> header, header -> payload 函数：
 * 因为每个块指向块头而不是负载，
 * 在从 malloc 返回时以及在释放块之前需要调整。
 * 
 */
static block_t *payload_to_header(void *bp) {
    /* 这里无法避免指针算术 */
    return (block_t *)(((char *)bp) - offsetof(block_t, payload));
}

static void *header_to_payload(block_t *block) {
    return (void *)(block->payload);
}

/* 将大小舍入到 multiple 的倍数 */
static size_t roundup(size_t size, size_t multiple) {
    return multiple * ((size + multiple - 1) / multiple);
}
