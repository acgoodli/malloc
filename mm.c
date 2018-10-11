/*
 * mm-naive.c - The fastest, least memory-efficient malloc package.
 * 
 * In this naive approach, a block is allocated by simply incrementing
 * the brk pointer.  A block is pure payload. There are no headers or
 * footers.  Blocks are never coalesced or reused. Realloc is
 * implemented directly using mm_malloc and mm_free.
 *
 * NOTE TO STUDENTS: Replace this header comment with your own header
 * comment that gives a high level description of your solution.
 */
#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <unistd.h>
#include <string.h>

#include "mm.h"
#include "memlib.h"

/*********************************************************
 * NOTE TO STUDENTS: Before you do anything else, please
 * provide your team information in the following struct.
 ********************************************************/
team_t team = {
    /* Team name */
    "TonyAvCo",
    /* First member's full name */
    "Tony Do",
    /* First member's email address */
    "tmdo@millersville.edu",
    /* Second member's full name (leave blank if none) */
    "Avree Goodling",
    /* Second member's email address (leave blank if none) */
    "acgoodling@millersville.edu"
};

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8


#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

#define PUT(p, val) (*(unsigned int *)(p) = (val))

static const size_t WORD_SIZE  = sizeof(size_t);     /* word size (bytes) */  
static const size_t DWORD_SIZE = 2 * WORD_SIZE;      /* doubleword size (bytes) */
static const size_t CHUNKSIZE  = (1<<12);            /* initial heap size (bytes) */
static const size_t OVERHEAD   = 2 * sizeof(size_t); /* overhead of header and footer (bytes) */

/* Helper Functions Given */

static inline size_t max (size_t a, size_t b) {
  return (a > b) ? a : b;
}

static inline size_t min (size_t a, size_t b) {
  return (a < b) ? a : b;
}

static inline size_t align (size_t size, size_t alignment) {
  return (size + (alignment - 1)) & ~(alignment - 1);
}

/*
 * Returns the data at p
 */
static inline size_t* data (void* p) {
    return (size_t*)p;
}

/*
 * Aligns the chunk to fit the word size
 */
static inline size_t alignTo (size_t requested, size_t align) {
    return (align * (requested + align - 1)) / align;
}

static inline _Bool isAlloc (void* ptr) {
  return *header(ptr) & 1;
}

static inline size_t packData (size_t size, _Bool alloc) {
  return size | (size_t)alloc;
}

static inline void setBlock (void* ptr, size_t data) {
  *header(ptr) = data;
  *footer(ptr) = data;
}

static inline size_t* nextBlock (void* ptr) {
  return (size_t*)ptr + sizeOf (ptr);
}

static inline size_t* prevBlock (void* ptr) {
  size_t* p = (size_t*)ptr;
  size_t* size = p - 2;
  return p - (*size & -2);
}

static inline size_t* header (void* ptr) {
  return ((size_t*)ptr) - 1;
}

static inline size_t sizeOf (void* ptr) {
  return *header(ptr) & -2;
}

static inline size_t* footer (void* ptr) {
  return (size_t*)ptr + sizeOf (ptr) - 2;
}

static inline size_t** nextPtr (void* ptr) {
  return (size_t**)ptr;
}

static inline size_t** prevPtr (void* ptr) {
  return (size_t**)nextPtr(ptr) + 1;
}

static inline void* nextFreeBlock (void* ptr) {
  return *nextPtr(ptr);
}

static inline void* prevFreeBlock (void* ptr) {
  return *prevPtr(ptr);
}

static inline void make_free_node (void* curr, size_t size) {
  void* prev = heap_listp;
  void* next = nextFreeBlock (prev);
  *header (curr) = packData (size, 0);
  *footer (curr) = packData (size, 0);
  *nextPtr (curr) = next;
  *prevPtr (curr) = prev;
  *nextPtr (prev) = curr;
  *prevPtr (next) = curr;
}

static inline void mark_free_node (void* cursor) {
  delete_free_node (cursor);
  *header (cursor) ^= 1;
  *footer (cursor) ^= 1;
}

static inline void delete_free_node (void* cursor) {
  void* prev = prevFreeBlock (cursor);
  void* next = nextFreeBlock (cursor);
  *nextPtr (prev) = next;
  *prevPtr (next) = prev;
}

/* You should only need ONE global variable */
size_t* list_root; //Keeps track of the beginning of the linked list


/* suggested function prototypes for internal helper routines */

static void* coalesce (void* bp);

/* extends heap by passed number of WORDS
 * returns the BLOCK POINTER of the new space added (or NULL if mem_sbrk returned -1)
 */
static void* extend_heap (size_t words)
{
  void* base = mem_sbrk (words * sizeof (size_t));
  if (base == (void*)-1) {
    return NULL;
  }
  make_free_node (base, words);
  *header (nextBlock (base)) = packData (0, 1);
  return coalesce (base);
}

/* 
 * place block of asize bytes at start of free block bp 
 * split if remainder would be at least minimum block size
 */
static inline void* place (void* cursor, size_t newSize) {
  mark_free_node (cursor);
  size_t splitSize = sizeOf (cursor) - newSize;
  if (splitSize >= MIN_BLOCK_SIZE) {
    setBlock (cursor, packData (newSize, 1));
    make_free_node (nextBlock (cursor), splitSize);
  }
  return cursor;
}


/* required functions */

/*
 * mm_init - initialize the malloc package.
 *
 *   0   1   2   3   4   5   ...
 * +---+---+---+---+---+---+---+---+---+---+
 * |   | 4*|   |   | 4*| 0*|   |   |   |   |
 * +---+---+---+---+---+---+---+---+---+---+
 *     ^               ^ ^
 *      \_____________/   \
 *          prologue        epilogue
 */
int mm_init (void) 
{
    /* create the initial empty heap
       NOTE: it should only be 4 words initially (refer to the diagram)

       hints:
            - allocate with mem_sbrk
            - initialize the four words to represent:
                1. alignment padding
                2. prologue header
                3. prologue footer
                4. epilogue header
            - update the pointer to refer to the heap list pointer to immediately after the prologue
            - extend empty heap to a free block of CHUNKSIZE bytes
    */

    //If we do not have enough memory
  size_t overhead = 4 * WORDSIZE;
  size_t* base = (size_t*)mem_sbrk (overhead);
  if (base == (size_t*)-1) {
    return -1;
  }
  list_root = base + 2;
  setBlock (list_root, packData (2, 1));
  *header (nextBlock (list_root)) = packData (0, 1);
  list_root = extend_heap (CHUNKSIZE);
  return 0;
}

/* 
 * mm_malloc - Allocate a block with at least size bytes of payload 
 */
void *mm_malloc (size_t size) 
{
    /* Adjust block size to include overhead and alignment reqs. */
    /* Search the free list for a fit */
    /* If no fit found: get more memory */
    /* place the block */
  size_t newSize = align (size + OVERHEAD, ALIGNMENT) / WORDSIZE;
  size_t* cursor = list_root;
  for (; sizeOf (cursor) != 0; cursor = nextBlock (cursor)) {
    if (sizeOf (cursor) >= newSize && !isAlloc (cursor)) {
      return place (cursor, newSize);
    }
  }
  cursor = extend_heap (max (CHUNKSIZE, newSize));
  return place (cursor, newSize);
}

/* 
 * mm_free - Free a block 
 */
void mm_free(void *ptr)
{
  make_free_node (ptr, sizeOf (ptr));
  coalesce (ptr);
}

/*
 * coalesce - boundary tag coalescing. Return ptr to coalesced block
 */
static size_t* coalesce (void* ptr) {
  void* begin = ptr;
  size_t size = sizeOf (ptr);
  if (!isAlloc (prevBlock (ptr))) {
    begin = prevBlock (ptr);
    size += sizeOf (prevBlock (ptr));
  }
  if (!isAlloc (nextBlock (ptr))) {
    size += sizeOf (nextBlock (ptr));
  }
  if (size != sizeOf (ptr)) {
    make_free_node (begin, size);
  }
  return begin;
}

/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 */
void* mm_realloc (void *ptr, size_t size)
{
  void* newPtr = mm_malloc (size);
  if (newPtr == NULL) {
    return NULL;
  }
  size_t copySize = min (size, WORDSIZE * sizeOf (ptr) - OVERHEAD);
  memcpy (newPtr, ptr, copySize);
  mm_free (ptr);
  return newPtr;
}