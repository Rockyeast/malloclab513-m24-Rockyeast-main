/**
 * @file mm.c
 * @brief 一个基于64位结构的隐式空闲链表内存分配器
 *
 * 15-213: 计算机系统导论
 *
 * TODO: 在这里插入你的文档。 :)
 *
 *************************************************************************
 *
 * 给学生的建议。
 * - 第0步：请阅读写作说明！
 * - 第1步：编写你的堆检查器。
 * - 第2步：编写契约/调试断言语句。
 * - 祝你好运，玩得开心！
 *
 *************************************************************************
 *
 * @author Zhifeng Li <zhifengl@andrew.cmu.edu>
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

/* 不要改变以下内容！ */

#ifdef DRIVER
/* 为driver测试创建别名 */
#define malloc mm_malloc
#define free mm_free
#define realloc mm_realloc
#define calloc mm_calloc
#define memset mem_memset
#define memcpy mem_memcpy
#endif /* def DRIVER */

/* 从这里开始你可以改变任何内容 */

/*
 *****************************************************************************
 * 如果定义了DEBUG（例如在运行mdriver-dbg时），这些宏将被启用。
 * 你可以在调试模式下使用它们来打印调试输出和检查契约。
 * 只有名字以"dbg_"开头的调试宏是允许的。你不能定义任何其他带参数的宏。
 *****************************************************************************
 */
#ifdef DEBUG
/* 当定义了DEBUG时，这些形成有用函数的别名 */
#define dbg_requires(expr) assert(expr)  //检查表达式是否为真，如果为假则程序会中断并输出错误信息
#define dbg_assert(expr) assert(expr)
#define dbg_ensures(expr) assert(expr) 
#define dbg_printf(...) ((void)printf(__VA_ARGS__))  //将参数传递给 printf 函数，用于输出调试信息
#define dbg_printheap(...) print_heap(__VA_ARGS__)  //调用 print_heap 函数，通常用于打印当前堆的状态
#else
/* 当没有定义DEBUG时，这些应该不生成任何代码，
 * 即使是参数表达式的计算也不生成。然而，参数表达式仍然应该进行语法检查，
   并且应该算作涉及的变量的使用。这以前使用了一个简单的黑客技术涉及sizeof()，
   但这有时会引起关于sizeof()误用的警告。我希望这个新的、更不直接的黑客技术会更稳健。
 * 向Stack Overflow发帖者chqrlie致敬（参见https://stackoverflow.com/questions/72647780）。
 */
#define dbg_discard_expr_(...) ((void)((0) && printf(__VA_ARGS__))) //使用 (void)((0) && printf(__VA_ARGS__))确保即使在非调试模式下，参数表达式也会进行语法检查和变量使用检查，但实际上不会执行任何操作
#define dbg_requires(expr) dbg_discard_expr_("%d", !(expr)) //下列宏都会使用 dbg_discard_expr_，所以在非调试模式下，它们的效果是相同的，即不生成任何代码
#define dbg_assert(expr) dbg_discard_expr_("%d", !(expr))
#define dbg_ensures(expr) dbg_discard_expr_("%d", !(expr))
#define dbg_printf(...) dbg_discard_expr_(__VA_ARGS__)
#define dbg_printheap(...) ((void)((0) && print_heap(__VA_ARGS__)))
#endif

/* 基本常数 */

typedef uint64_t word_t; //word_t是一个 64 位（8 字节）的无符号整数

/** @brief 字和头大小（字节） */
static const size_t wsize = sizeof(word_t);

/** @brief 双字大小（字节） */
static const size_t dsize = 2 * wsize;

/** @brief 最小块大小（字节） */
static const size_t min_block_size = 2 * dsize;

/**
 * TODO: 解释chunksize是什么
 * （必须能被dsize整除）
 * chunksize 是指扩展堆时请求的内存块的大小。
 * 这个大小通常是系统页面大小的倍数（例如 1 << 12，即4096 字节，即 4 KB），
 * 它确保每次堆扩展都能获得足够大的连续内存块，
 * 以便更高效地分配内存。chunksize 必须是 dsize 的倍数，以保证内存对齐
 */
static const size_t chunksize = (1 << 12);

/**
 * TODO: 解释alloc_mask是什么
 * alloc_mask 是用于提取和设置块分配标志的掩码。
 * 它是一个位掩码，最低位为 1。
 * 当块被分配时，该位设置为 1；当块空闲时，该位设置为 0。
 * 通过使用 alloc_mask，可以方便地检查和修改块的分配状态
 */
static const word_t alloc_mask = 0x1;

/**
 * TODO: 解释size_mask是什么
 * size_mask 是用于提取块大小的掩码。因为堆块的大小是 16 字节对齐的，
 * 所以块的大小信息存储在头部的高位，而低 4 位用于存储分配标志和其他元数据。
 * 通过与 size_mask 进行按位与操作
 * 可以屏蔽掉头部的低 4 位，只保留高位的块大小信息
 */
static const word_t size_mask = ~(word_t)0xF; //0xFFFFFFFFFFFFFFF0，忽略低4位

/** @brief 表示堆中一个块的头和有效载荷 */
typedef struct block {
    /** @brief 头包含大小+分配标志 */
    word_t header;

    /**
     * @brief 指向块有效载荷的指针。
     *
     * TODO: 仔细阅读后可以删除此注释。
     * 我们不知道有效载荷的大小是多少，所以我们将其声明为零长度数组，
     * 这是GNU编译器扩展。这样我们就可以获得指向有效载荷开始位置的指针。
     * （类似的标准C特性“灵活数组成员”在这里不起作用，
     *  因为它们不能作为联合的成员。）
     *
     * 警告：零长度数组必须是结构的最后一个元素，
     * 所以在它之后不应该有任何结构字段。
     * 对于这个实验室，我们将允许你在联合中包含一个零长度数组，
     * 只要联合是其包含结构中的最后一个字段。
     * 然而，这是编译器特定的行为，通常应该避免。
     *
     * 警告：不要将这个指针转换为/从其他类型！
     * 相反，你应该使用联合将这个零长度数组与另一个结构别名，
     * 以便在有效载荷内存中存储其他类型的数据。
     */
    char payload[0];

    /*
     * TODO: 一旦你思考过这个问题，可以删除或替换这个注释。
     * 为什么我们不能在这里声明块的尾部作为结构的一部分？
        ▪ 块的尾部通常用于存储和头部相同的信息，用于实现双向链表或其他需要的功能。
        ▪ 将尾部包含在结构中会使得结构的定义复杂化，并且不利于灵活管理不同大小的内存块。

     * 为什么我们甚至需要尾部——代码在没有它们的情况下能正常工作吗？
        ▪ 尾部在某些内存管理算法中是必须的，比如在合并空闲块时，需要知道前一个块的状态。
        ▪ 没有尾部，代码在某些情况下可能会无法正确处理合并操作。

     * 哪些函数实际使用了尾部中的数据？
        ▪ 它通常在分配器代码中作为一个单独的字段来处理
        ▪ 合并空闲块的函数，例如 coalesce_block
        ▪ 用于遍历内存块的函数，需要从一个块移动到下一个块或前一个块
     */
} block_t;

/* 全局变量 */

/** @brief 指向堆中第一个块的指针 */
static block_t *heap_start = NULL;

/*
 *****************************************************************************
 * 下面的函数是用于进行位操作、指针算术和其他辅助操作的简短包装函数。
 * 我们已经为你提供了下面函数的函数头注释，以帮助你理解这些基本代码的工作原理。
 * 注意这些函数头注释是简短的，因为它们描述的函数也是简短的；
 * 对于你自己编写的函数，你需要提供足够详细的说明！
 *****************************************************************************
 */

/*
 * ---------------------------------------------------------------------------
 *                        开始简短辅助函数
 * ---------------------------------------------------------------------------
 */

/**
 * @brief 返回两个整数中的最大值。
 * @param[in] x
 * @param[in] y
 * @return `x`如果`x > y`，否则返回`y`。
 */
static size_t max(size_t x, size_t y) {
    return (x > y) ? x : y;
}

/**
 * @brief 将`size`向上舍入到下一个n的倍数
 * @param[in] size
 * @param[in] n
 * @return 舍入后的大小
 */
static size_t round_up(size_t size, size_t n) {
    return n * ((size + (n - 1)) / n);
}

/**
 * @brief 将块的`size`和`alloc`打包成一个适合用作打包值的字。
 *
 * 打包值用于头和尾。
 *
 * 分配状态打包在字的最低位。
 *
 * @param[in] size 表示块的大小
 * @param[in] alloc 如果块被分配则为真
 * @return 打包值
 */
static word_t pack(size_t size, bool alloc) {
    word_t word = size;
    if (alloc) {
        word |= alloc_mask; //按位或操作,最低位置为 1，表示该块已分配
    }
    return word;
}

/**
 * @brief 提取打包字中表示的大小。
 *
 * 这个函数简单地清除字的最低4位，因为堆是16字节对齐的。
 *
 * @param[in] word
 * @return 由该字表示的块的大小
 */
static size_t extract_size(word_t word) {
    return (word & size_mask);
}

/**
 * @brief 从块的头部提取块的大小。
 * @param[in] block
 * @return 块的大小
 */
static size_t get_size(block_t *block) {
    return extract_size(block->header);
}

/**
 * @brief 给定一个有效载荷指针，返回对应块的指针。
 * @param[in] bp 指向块的有效载荷的指针
 * @return 对应的块
 */
static block_t *payload_to_header(void *bp) {
    return (block_t *)((char *)bp - offsetof(block_t, payload)); //有效载荷-payload
}

/**
 * @brief 给定一个块指针，返回对应有效载荷的指针。
 * @param[in] block
 * @return 指向块有效载荷的指针
 * @pre 块必须是一个有效块，而不是边界标签。
 */
static void *header_to_payload(block_t *block) {
    dbg_requires(get_size(block) != 0);
    return (void *)(block->payload);
}

/**
 * @brief 给定一个块指针，返回对应尾部的指针。
 * @param[in] block
 * @return 指向块尾部的指针
 * @pre 块必须是一个有效块，而不是边界标签。
 */
static word_t *header_to_footer(block_t *block) {
    dbg_requires(get_size(block) != 0 &&
                 "Called header_to_footer on the epilogue block");
    return (word_t *)(block->payload + get_size(block) - dsize);
}

/**
 * @brief 给定块的尾部，返回对应的头部指针。
 *
 * 头部通过从尾部减去块大小并加回wsize来找到。
 *
 * 如果给出序言，则将尾部返回为块。
 *
 * @param[in] footer 指向块尾部的指针
 * @return 指向块开始的指针
 */
static block_t *footer_to_header(word_t *footer) {
    size_t size = extract_size(*footer);
    if (size == 0){
        return (block_t *)footer;
    }
    return (block_t *)((char *)footer + wsize - size);
}

/**
 * @brief 返回给定块的有效载荷大小。
 *
 * 有效载荷大小等于整个块大小减去块的头部和尾部大小。
 *
 * @param[in] block
 * @return 块的有效载荷大小
 */
static size_t get_payload_size(block_t *block) {
    size_t asize = get_size(block);
    return asize - dsize;
}

/**
 * @brief 返回给定头部值的分配状态。
 *
 * 这是基于头部值的最低位。
 *
 * @param[in] word
 * @return 与该字对应的分配状态
 */
static bool extract_alloc(word_t word) {
    return (bool)(word & alloc_mask);
}

/**
 * @brief 返回块的分配状态，基于其头部。
 * @param[in] block
 * @return 块的分配状态
 */
static bool get_alloc(block_t *block) {
    return extract_alloc(block->header);
}

/**
 * @brief 在给定地址写入一个结束头部。
 *
 * 结束头部大小为0，并标记为已分配。
 *
 * @param[out] block 写入结束头部的位置
 */
static void write_epilogue(block_t *block) {
    dbg_requires(block != NULL);
    dbg_requires((char *)block == (char *)mem_heap_hi() - 7);
    block->header = pack(0, true);
}

/**
 * @brief 在给定地址写入一个块。
 *
 * 此函数写入头部和尾部，其中尾部的位置是相对于头部计算的。
 *
 * TODO: 是否有任何前置条件或后置条件？
 * @pre
 * - `block` 不为空。
 * - `size` 大于 0，表示有效的块大小。
 * - `block` 指向的内存区域足够大，可以容纳头部、有效载荷和尾部。
 *
 * @post
 * - 给定地址 `block` 处将写入一个新的块头部和尾部。
 * - 头部和尾部都包含块的大小和分配状态。
 * - 块的头部和尾部正确设置并且一致。
 * 
 * @param[out] block 开始写入块头部的位置
 * @param[in] size 新块的大小
 * @param[in] alloc 新块的分配状态
 */
static void write_block(block_t *block, size_t size, bool alloc) {
    dbg_requires(block != NULL);
    dbg_requires(size > 0);
    block->header = pack(size, alloc);
    word_t *footerp = header_to_footer(block);
    *footerp = pack(size, alloc);
}

/**
 * @brief 找到堆中下一个连续的块。
 *
 * 这个函数通过添加块的大小来访问堆中的“隐式列表”中的下一个块。
 *
 * @param[in] block 堆中的一个块
 * @return 堆中的下一个连续块
 * @pre 块不是结束块
 */
static block_t *find_next(block_t *block) {
    dbg_requires(block != NULL);
    dbg_requires(get_size(block) != 0 &&
                 "Called find_next on the last block in the heap");
    return (block_t *)((char *)block + get_size(block));
}

/**
 * @brief 找到堆中上一个块的尾部。
 * @param[in] block 堆中的一个块
 * @return 上一个块的尾部位置
 */
static word_t *find_prev_footer(block_t *block) {
    // 计算前一个块的尾部位置，位置在当前块头部之前的一个字处
    return &(block->header) - 1;
}

/**
 * @brief 查找堆中前一个连续的块。
 *
 * 这是堆中的“隐式链表”中的前一个块。
 *
 * 通过读取前一个块的页脚来确定其大小，然后根据其大小计算前一个块的起始位置。
 *
 * @param[in] block 堆中的一个块
 * @return 堆中前一个连续的块。
 * @pre 该块不是序言块
 */
static block_t *find_prev(block_t *block) {
    dbg_requires(block != NULL);
    dbg_requires(get_size(block) != 0 &&
                 "Called find_prev on the first block in the heap");
    word_t *footerp = find_prev_footer(block);
    return footer_to_header(footerp);
}

/*
 * ---------------------------------------------------------------------------
 *                        结束简短辅助函数
 * ---------------------------------------------------------------------------
 */

/******** 以下内容为辅助和调试例程 ********/

/**
 * @brief 合并空闲块。
 *
 * 该函数合并当前块与前后相邻的空闲块，以减少内存碎片。它根据前一个块和下一个块的分配状态，
 * 选择合并的方式，并返回合并后的块。
 *
 * @param[in] block 指向要合并的内存块的指针。
 * @return 返回合并后的内存块指针。
 *
 * @pre `block` 必须是一个有效的、标记为空闲的块。
 * @post 返回的块可能是合并后的块，并且其大小可能增大。
 */
static block_t *coalesce_block(block_t *block) {
    dbg_requires(block != NULL);
    dbg_requires(!get_alloc(block));
    
    block_t *prev_block = find_prev(block);
    block_t *next_block = find_next(block);
    size_t prev_alloc = get_alloc(prev_block);
    size_t next_alloc = get_alloc(next_block);
    size_t size = get_size(block);

    if (prev_alloc && next_alloc) {                 // 情况 1：前一个块和下一个块都已分配
        // 无需合并
    } else if (prev_alloc && !next_alloc) {         // 情况 2：下一个块是空闲的
        size += get_size(next_block);
        write_block(block, size, false);
    } else if (!prev_alloc && next_alloc) {         // 情况 3：前一个块是空闲的
        size += get_size(prev_block);
        block = prev_block;
        write_block(block, size, false);
    } else {                                        // 情况 4：前一个块和下一个块都是空闲的
        size += get_size(prev_block) + get_size(next_block);
        block = prev_block;
        write_block(block, size, false);
    }

    dbg_ensures(!get_alloc(block));
    return block;
}

/**
 * @brief 扩展堆的大小。
 *
 * 这个函数扩展堆的大小，分配一个新的空闲块，并初始化该块的头和尾。 
 * 如果前一个块是空闲的，则进行合并。
 *
 * @param[in] size 需要扩展的大小（字节数）。
 * @return 成功时返回指向新分配块的指针，失败时返回 NULL。
 *
 * @pre size 必须是非负数。
 * @post 返回的块已经正确初始化，并且堆的大小已增加。
 */
static block_t *extend_heap(size_t size) {
    void *bp;

    // 分配偶数个字以保持对齐
    size = round_up(size, dsize);
    if ((bp = mem_sbrk((intptr_t)size)) == (void *)-1) {
        return NULL;
    }

    /*
     * TODO: 思考后删除或替换此注释。
     * 思考 bp 代表什么。
     * bp 代表新分配的堆内存区域的起始地址。我们从 bp 前一个字开始写新的块
     * 
     * 为什么我们从 bp 前一个字开始写新的块，但请求的大小相同？
     * 是为了确保头部和尾部的对齐，同时保持块大小不变。
     * 这样可以保证内存的正确管理。
     */

    // 初始化空闲块头/
    block_t *block = payload_to_header(bp);
    write_block(block, size, false);

    // 创建新的尾部头
    block_t *block_next = find_next(block);
    write_epilogue(block_next);

    // 如果前一个块是空闲的，则进行合并
    block = coalesce_block(block);

    return block;
}

/**
 * @brief 拆分一个已分配的块，如果其大小大于请求的大小。
 *
 * 该函数检查已分配块的大小是否大于请求的大小 `asize`。如果是，
 * 则将其拆分为两个块：一个大小为 `asize` 的已分配块和一个新的空闲块。
 *
 * @param[in] block 指向要拆分的内存块的指针。
 * @param[in] asize 请求的块的大小，以字节为单位。
 *
 * @pre `block` 必须是一个已分配的块。
 * @pre `asize` 必须小于或等于 `block` 的大小，并且满足最小块大小要求。
 * @post 如果 `block` 的大小大于 `asize`，则 `block` 被拆分为两个块，
 *       一个大小为 `asize` 的已分配块和一个新的空闲块。
 */
static void split_block(block_t *block, size_t asize) {
    dbg_requires(get_alloc(block));
    /* TODO: 你能写一个关于asize值的前置条件吗？ 
    * @pre `asize` 必须小于或等于 `block` 的大小，并且满足最小块大小要求。*/

    size_t block_size = get_size(block);

    if ((block_size - asize) >= min_block_size) {
        block_t *block_next;
        write_block(block, asize, true);

        block_next = find_next(block);
        write_block(block_next, block_size - asize, false);
    }

    dbg_ensures(get_alloc(block));
}

/**
 * @brief 在空闲链表中查找一个适合的块。
 *
 * 该函数在空闲链表中查找一个大小至少为 `asize` 字节的空闲块。
 * 如果找到合适的块，则返回指向该块的指针；否则，返回 `NULL`。
 *
 * @param[in] asize 需要查找的块的最小大小，以字节为单位。
 * @return 成功时返回指向找到的空闲块的指针；如果找不到合适的块，返回 `NULL`。
 *
 * @pre `asize` 必须为正数。
 * @post 如果找到合适的块，返回指向该块的指针；否则，返回 `NULL`。
 */
static block_t *find_fit(size_t asize) {
    block_t *block;

    for (block = heap_start; get_size(block) > 0; block = find_next(block)) {

        if (!(get_alloc(block)) && (asize <= get_size(block))) {
            return block;
        }
    }
    return NULL; // 找不到合适的块
}

/**
 * @brief 检查堆的一致性。
 *
 * 该函数检查堆的一致性，包括头块和尾块、地址对齐、堆边界、头部和尾部匹配、
 * 块合并情况、空闲列表的前后指针一致性、空闲列表指针在堆范围内，以及
 * 通过遍历空闲块来检查是否匹配。
 *
 * @param[in] line 调用检查器的行号。
 * @return 如果堆一致性检查通过，返回 true；如果发现任何错误，返回 false。
 */
bool mm_checkheap(int line) {
    block_t *block;
    bool prev_alloc = true;

    // 检查头块
    if (get_size(heap_start) == 0 || !get_alloc(heap_start)) {
        fprintf(stderr, "Error: Bad prologue header\n");
        return false;
    }

    // 检查每个块
    for (block = heap_start; get_size(block) > 0; block = find_next(block)) {
        // 检查地址对齐
        if ((size_t)block % dsize != 0) {
            fprintf(stderr, "Error: %p is not doubleword aligned\n", block);
            return false;
        }

        // 检查块是否位于堆边界内
        if ((char *)block < (char *)mem_heap_lo() || (char *)block > (char *)mem_heap_hi()) {
            fprintf(stderr, "Error: %p is out of heap bounds\n", block);
            return false;
        }

        // 检查头部和尾部大小是否匹配
        if (get_size(block) != extract_size(*header_to_footer(block))) {
            fprintf(stderr, "Error: header and footer size mismatch\n");
            return false;
        }

        // 检查前一个/下一个分配/空闲位一致性
        if (prev_alloc && !get_alloc(block)) {
            prev_alloc = false;
        } else if (!prev_alloc && !get_alloc(block)) {
            fprintf(stderr, "Error: consecutive free blocks\n");
            return false;
        } else {
            prev_alloc = get_alloc(block);
        }
    }

    // 检查尾块
    if (get_size(block) != 0 || !get_alloc(block)) {
        fprintf(stderr, "Error: Bad epilogue header\n");
        return false;
    }

    // 检查空闲列表
    // 假设有一个空闲列表 free_list
    for (block = free_list; block != NULL; block = next_free(block)) {
        // 检查前后指针一致性
        if (prev_free(block) != NULL && next_free(prev_free(block)) != block) {
            fprintf(stderr, "Error: inconsistent next/prev pointers\n");
            return false;
        }
        if (next_free(block) != NULL && prev_free(next_free(block)) != block) {
            fprintf(stderr, "Error: inconsistent prev/next pointers\n");
            return false;
        }

        // 检查空闲列表指针是否在堆范围内
        if ((char *)block < (char *)mem_heap_lo() || (char *)block > (char *)mem_heap_hi()) {
            fprintf(stderr, "Error: free block %p is out of heap bounds\n", block);
            return false;
        }

        // 检查每个列表桶中的所有块是否在桶大小范围内
        // 假设有一个函数 get_bucket_size 用于获取桶大小
        size_t bucket_size = get_bucket_size(block);
        if (get_size(block) > bucket_size) {
            fprintf(stderr, "Error: free block %p size is out of bucket size range\n", block);
            return false;
        }
    }

    return true;
}


/**
 * @brief 初始化内存分配器。
 * @return 如果初始化成功返回 true，否则返回 false
 * @pre 堆尚未初始化。
 * @post 如果函数返回 true，则堆已正确初始化并且准备好进行内存分配。
         如果函数返回 false，则初始化失败，分配器不可用。
 
   堆序言块         空闲块         已分配块          空闲块        堆结尾块
+------------+  +------------+  +------------+  +------------+  +------------+
|  Header    |  |  Header    |  |  Header    |  |  Header    |  |  Header    |
|  (Size,    |  |  (Size,    |  |  (Size,    |  |  (Size,    |  |  (Size,    |
|  Alloc)    |  |  Alloc)    |  |  Alloc)    |  |  Alloc)    |  |  Alloc)    |
+------------+  +------------+  +------------+  +------------+  +------------+
|  Footer    |  |  Footer    |  |  Payload   |  |  Footer    |  |            |
|  (Size,    |  |  (Size,    |  |            |  |  (Size,    |  |            |
|  Alloc)    |  |  Alloc)    |  |            |  |  Alloc)    |  |            |
+------------+  +------------+  +------------+  +------------+  +------------+
*/

bool mm_init(void) {
    // 创建初始的空堆
    word_t *start = (word_t *)(mem_sbrk(2 * wsize));

    if (start == (void *)-1) {
        return false;
    }

    /*
     * 堆序言和堆结尾分别对应于块的尾部和头部，
       它们的作用是简化边界条件的处理，尤其是在合并空闲块时。
     * 堆序言标记堆的开始，堆结尾标记堆的结束，
       它们确保在进行块操作时不会越界访问。
     */

    start[0] = pack(0, true); // 堆序言（块尾部）
    start[1] = pack(0, true); // 堆结尾（块头部）

    // 堆从第一个“块头部”开始，目前是结尾
    heap_start = (block_t *)&(start[1]);

    // 用 chunksize 字节的空闲块扩展空堆
    if (extend_heap(chunksize) == NULL) { //extend_heap要看下
        return false;
    }

    return true;
}

/**
 * @brief 分配指定大小的内存块。good
 *
 * 该函数分配一个大小至少为 size 字节的内存块，并返回指向该内存块的指针。
 * 如果当前堆中没有合适的空闲块，则会扩展堆的大小以满足请求。
 *
 * @param[in] size 需要分配的内存块大小，以字节为单位。
 * @return 成功时返回指向已分配内存块的指针；如果分配失败，返回 NULL。
 *
 * @pre size 必须为非负数。如果 size 为 0，函数将返回 NULL。
 * @post 返回的指针指向一个大小至少为 size 字节的已分配内存块，
 *       并且该内存块在堆中正确初始化。
 */
void *malloc(size_t size) {
    dbg_requires(mm_checkheap(__LINE__));

    size_t asize;      // 调整后的块大小
    size_t extendsize; // 如果没有找到合适的块，需要扩展堆的大小
    block_t *block;
    void *bp = NULL;

    // 如果堆没有初始化，则初始化堆
    if (heap_start == NULL) {
        if (!(mm_init())) {
            dbg_printf("Problem initializing heap. Likely due to sbrk");
            return NULL;
        }
    }

    // 忽略无效的请求
    if (size == 0) {
        dbg_ensures(mm_checkheap(__LINE__));
        return bp;
    }

    // 调整块大小以包含开销并满足对齐要求
    asize = round_up(size + dsize, dsize);

    // 在空闲链表中查找合适的块
    block = find_fit(asize);

    // 如果没有找到合适的块，请求更多内存，然后放置块
    if (block == NULL) {
        // 总是至少请求 chunksize
        extendsize = max(asize, chunksize);
        block = extend_heap(extendsize);
        // extend_heap 返回错误
        if (block == NULL) {
            return bp;
        }
    }

    // 该块应标记为空闲
    dbg_assert(!get_alloc(block));

    // 将块标记为已分配
    size_t block_size = get_size(block);
    write_block(block, block_size, true);

    // 如果块太大，则尝试拆分块
    split_block(block, asize);

    bp = header_to_payload(block);

    dbg_ensures(mm_checkheap(__LINE__));
    return bp;
}

/**
 * @brief 释放指定的内存块。
 *
 * 该函数释放由 `malloc` 或 `realloc` 分配的内存块，并将其标记为空闲。
 * 同时尝试与相邻的空闲块合并，以减少内存碎片。
 *
 * @param[in] bp 指向要释放的内存块的指针。
 *
 * @pre `bp` 必须是由 `malloc` 或 `realloc` 返回的有效指针，且不能为 NULL。
 * @post 内存块 `bp` 已被标记为空闲，并且可能已与相邻的空闲块合并。
 *
 * @param[in] bp
 */
void free(void *bp) {
    dbg_requires(mm_checkheap(__LINE__));

    if (bp == NULL) {
        return;
    }

    block_t *block = payload_to_header(bp);
    size_t size = get_size(block);

    // 该块应标记为已分配
    dbg_assert(get_alloc(block));

    // 将块标记为空闲
    write_block(block, size, false);

    // 尝试与其邻居合并块
    coalesce_block(block);

    dbg_ensures(mm_checkheap(__LINE__));
}

/**
 * @brief 重新分配指定大小的内存块。
 *
 * 该函数调整由 `malloc`、`calloc` 或 `realloc` 分配的内存块的大小。
 * 如果 `ptr` 为 `NULL`，则该函数等同于 `malloc`。
 * 如果 `size` 为 0，则该函数等同于 `free`，并返回 `NULL`。
 * 否则，该函数分配一个新的内存块，将旧内存块的数据复制到新内存块，并释放旧内存块。
 *
 * @param[in] ptr 指向要重新分配的内存块的指针。
 * @param[in] size 新内存块的大小，以字节为单位。
 * @return 成功时返回指向新内存块的指针；如果分配失败，返回 `NULL`。
 *
 * @pre `ptr` 必须是由 `malloc``calloc``realloc` 返回的有效指针，或为 `NULL`。
 * @post 返回的指针指向一个大小至少为 `size` 字节的新内存块，
 *       并且旧内存块的数据已复制到新内存块。
 *       如果 `size` 为 0，则返回 `NULL`，并释放原内存块。
 */
void *realloc(void *ptr, size_t size) {
    block_t *block = payload_to_header(ptr);
    size_t copysize;
    void *newptr;

    // 如果 size == 0，则释放块并返回 NULL
    if (size == 0) {
        free(ptr);
        return NULL;
    }

    // 如果 ptr 为 NULL，则等同于 malloc
    if (ptr == NULL) {
        return malloc(size);
    }

    // 否则，继续重新分配
    newptr = malloc(size);

    // 如果 malloc 失败，原始块保持不变
    if (newptr == NULL) {
        return NULL;
    }

    // 复制旧数据
    copysize = get_payload_size(block); // 获取旧有效负载的大小
    if (size < copysize) {
        copysize = size;
    }
    memcpy(newptr, ptr, copysize);

    // 释放旧块
    free(ptr);

    return newptr;
}

/**
 * @brief 分配并清零内存块。
 *
 * 该函数分配一个数组用于存储 `elements` 个大小为 `size` 字节的元素，
 * 并将所有字节初始化为零。如果乘法 `elements * size` 导致溢出，
 * 或者分配失败，函数返回 `NULL`。
 *
 * @param[in] elements 要分配的元素个数。
 * @param[in] size 每个元素的大小，以字节为单位。
 * @return 成功时返回指向已分配内存块的指针；如果分配失败，返回 `NULL`。
 *
 * @pre `elements` 和 `size` 必须为非负数。
 * @post 返回的指针指向一个大小至少为 `elements * size` 字节的内存块，
 * 且该内存块中的所有字节均已初始化为零。如果分配失败，返回 `NULL`。
 */
void *calloc(size_t elements, size_t size) {
    void *bp;
    size_t asize = elements * size;

    if (elements == 0) {
        return NULL;
    }
    if (asize / elements != size) {
        // 乘法溢出
        return NULL;
    }

    bp = malloc(asize);
    if (bp == NULL) {
        return NULL;
    }

    // 初始化所有位为 0
    memset(bp, 0, asize);

    return bp;
}

/*
 *****************************************************************************
 * 请勿删除以下超级机密（tm）行！                       *
 *                                                                           *
 * 53 6f 20 79 6f 75 27 72 65 20 74 72 79 69 6e 67 20 74 6f 20               *
 *                                                                           *
 * 66 69 67 75 72 65 20 6f 75 74 20 77 68 61 74 20 74 68 65 20               *
 * 68 65 78 61 64 65 63 69 6d 61 6c 20 64 69 67 69 74 73 20 64               *
 * 6f 2e 2e 2e 20 68 61 68 61 68 61 21 20 41 53 43 49 49 20 69               *
 *                                                                           *
 * 73 6e 27 74 20 74 68 65 20 72 69 67 68 74 20 65 6e 63 6f 64               *
 * 69 6e 67 21 20 4e 69 63 65 20 74 72 79 2c 20 74 68 6f 75 67               *
 * 68 21 20 2d 44 72 2e 20 45 76 69 6c 0a c5 7c fc 80 6e 57 0a               *
 * 所以你在尝试搞清楚这些十六进制数字的作用……哈哈哈！
 * ASCII不是正确的编码！不过不错的尝试！ - 邪恶博士                                                                          *
 *****************************************************************************
 */
