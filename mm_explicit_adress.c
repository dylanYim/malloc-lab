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
#include <sys/mman.h>
#include <errno.h>
#include "mm.h"
#include "memlib.h"

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

/*Basic constants and macros*/
#define WSIZE     4  /*워드 크기*/
#define DSIZE     8  /*더블 워드 크기*/
#define CHUNKSIZE (1<<12)  /*초기 가용 블럭과 힙 확장을 위한 기본 크기*/

#define MAX(x, y) ((x) > (y) ? (x) : (y))  /*x, y 중 큰 값*/

/*Pack a size and allocated bit into a word*/
#define PACK(size, alloc)  ((size) | (alloc))  /*블록의 크기와 할당여부 비트를 통합 -> 헤더와 풋터에 저장되는 값*/

/* Read and wirte a word at adress p*/
#define GET(p)      (*(unsigned int *)(p)) /*p가 참조하는 워드를 읽어서 리턴*/
#define PUT(p, val) (*(unsigned int *)(p) = (val)) /*p가 가리키는 워드에 val을 저장*/

/* Read the size and allocated fileds from address p*/
#define GET_SIZE(p)   (GET(p) & ~0x7) /*헤더나 풋터의 size 값을 리턴*/
#define GET_ALLOC(p)  (GET(p) & 0x1)  /*헤더나 풋터의 할당비트를 리턴*/

/* Given block ptr bp, compute address of its header and footer */
#define HDRP(bp)   ((char *)(bp) - WSIZE) /*bp 가 참조하는 블록의 헤더 리턴*/
#define FTRP(bp)   ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)  /*bp 가 참조하는 블록의 풋터 리턴*/


/* Given block ptr bp, compute address of next and previous blocks */
#define NEXT_BLKP(bp)  ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))  /*bp가 참조하는 블록의 다음 블록 리턴*/
#define PREV_BLKP(bp)  ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))  /*bp가 참조하는 블록의 이전 블록 리턴*/

#define PREDP(bp)  (*(void **)(bp))
#define SUCCP(bp)  (*(void **)(bp + WSIZE))

static void *heap_listp;
//static void *start_find_bp = NULL;
static void *root_free_bp;

static void *coalesce(void *bp);
static void *extend_heap(size_t words);
static void *find_fit(size_t asize);
static void place(void *bp, size_t asize);
void remove_free_list(void *bp);
void add_free_list(void *bp);

#define FIRST_FIT
//#define NEXT_FIT
//#define BEST_FIT

int mm_init(void)
{
  /* Create the initial empty heap*/
  heap_listp = mem_sbrk(6 * WSIZE);
  if (heap_listp == (void *) - 1) {
    return -1;
  }
  PUT(heap_listp, 0);
  PUT(heap_listp + (1*WSIZE), PACK(16, 1));
  PUT(heap_listp + (2*WSIZE), NULL);
  PUT(heap_listp + (3*WSIZE), NULL);
  PUT(heap_listp + (4*WSIZE), PACK(16, 1));
  PUT(heap_listp + (5*WSIZE), PACK(0, 1));

  root_free_bp = heap_listp + DSIZE;
//  start_find_bp = heap_listp + DSIZE;
  /*Extend the empty heap with a free block of CHUNKSIZE bytes*/
  if (extend_heap(CHUNKSIZE / WSIZE) == NULL) {
    return -1;
  }
  return 0;
}

static void *coalesce(void *bp){
  size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
  size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
  size_t size = GET_SIZE(HDRP(bp));

  if (prev_alloc && !next_alloc) {
    remove_free_list(NEXT_BLKP(bp));
    size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
  } else if (!prev_alloc && next_alloc) {
    remove_free_list(PREV_BLKP(bp));
    size += GET_SIZE(HDRP(PREV_BLKP(bp)));
    bp = PREV_BLKP(bp);
    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
  } else if(!prev_alloc && !next_alloc) {
    remove_free_list(PREV_BLKP(bp));
    remove_free_list(NEXT_BLKP(bp));
    size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(FTRP(NEXT_BLKP(bp)));
    PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
    PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
    bp = PREV_BLKP(bp);
  }
//  start_find_bp = bp;
  add_free_list(bp);
  return bp;
}

static void *extend_heap(size_t words){
  char *bp;
  size_t size;

  /*Allocate an even number of words to maintain alignment*/
  size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE;
  if (((bp = mem_sbrk(size)) == (void *)-1)) {
    return NULL;
  }

  /*Initialize free block header/footer and the epilogue header*/
  PUT(HDRP(bp), PACK(size, 0));
  PUT(FTRP(bp), PACK(size, 0));
  PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1));

  /*Coalesce if the previous block was free*/
  return coalesce(bp);
}

void *find_fit(size_t asize){/*First-fit search*/
  void *bp;

#ifdef FIRST_FIT
    for (bp = root_free_bp; GET_ALLOC(HDRP(bp)) == 0; bp = SUCCP(bp)) {
      if (asize <= GET_SIZE(HDRP(bp))) {
        return bp;
      }
    }
    return NULL; /*NO fit*/
#endif

#ifdef NEXT_FIT
  for (bp = start_find_bp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)) {
    if (!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp)))) {
      return bp;
    }
  }
  for (bp = heap_listp; bp != start_find_bp; bp = NEXT_BLKP(bp)) {
    if (!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp)))) {
      return bp;
    }
  }
    return NULL; /*NO fit*/
#endif

#ifdef BEST_FIT
  void *min_bp;
  int min_size = CHUNKSIZE;
  int is_find = 0;
  for (bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)) {

    if (!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp))) && (min_size < GET_SIZE(HDRP(bp)))) {
      min_bp = bp;
      is_find = 1;
    }
  }
  if (is_find) {
    return min_bp;
  } else {
    return NULL; /*NO fit*/
  }
#endif
}

static void place(void *bp, size_t asize){
  size_t csize = GET_SIZE(HDRP(bp));
  remove_free_list(bp);
  if ((csize - asize) >= (2 * DSIZE)) {
    PUT(HDRP(bp), PACK(asize, 1));
    PUT(FTRP(bp), PACK(asize, 1));
    bp = NEXT_BLKP(bp);
    PUT(HDRP(bp), PACK(csize - asize, 0));
    PUT(FTRP(bp), PACK(csize - asize, 0));
    add_free_list(bp);
//    start_find_bp = bp;
  } else {
    PUT(HDRP(bp), PACK(csize, 1));
    PUT(FTRP(bp), PACK(csize, 1));
  }
}
/* 
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 */
void *mm_malloc(size_t size)
{
  size_t asize;
  size_t extendsize;
  void* bp;

  /* Ignore spurious requests*/
  if (size <= 0) {
    return NULL;
  }

  /* Adjust block size to include overhead and alignment reqs*/
  if (size <= DSIZE) {
    asize = 2 * DSIZE;
  } else {
    asize = DSIZE * ((size + (DSIZE) + (DSIZE - 1)) / DSIZE);
  }

  /*Search the free list for a fit*/
  if ((bp = find_fit(asize)) != NULL) {
    place(bp, asize);
    return bp;
  }

  /*No fit found. Get more memory and place the block*/
  extendsize = MAX(asize, CHUNKSIZE);
  if ((bp = extend_heap(extendsize / WSIZE)) == NULL) {
    return NULL;
  }
  place(bp, asize);
  return bp;
}

void remove_free_list(void *bp){
  if (bp == root_free_bp) {
    PREDP(SUCCP(bp)) = NULL;
    root_free_bp = SUCCP(bp);
  } else {
    SUCCP(PREDP(bp)) = SUCCP(bp);
    PREDP(SUCCP(bp)) = PREDP(bp);
  }
}

void add_free_list(void *bp){
  unsigned int bp_address = *((unsigned int *)(bp));
  void *curr = root_free_bp;
  while(bp_address > *((unsigned int *)curr) && SUCCP(curr) != NULL){
    curr = SUCCP(curr);
  }

  if (curr == (unsigned int *) root_free_bp) {
    PREDP(curr) = bp;
    SUCCP(bp) = curr;
    root_free_bp = bp;
  } else {
    SUCCP(PREDP(curr)) = bp;
    PREDP(bp) = PREDP(curr);
    SUCCP(bp) = curr;
    PREDP(curr) = bp;
  }
}

/*
 * mm_free - Freeing a block does nothing.
 */
void mm_free(void *ptr)
{
  size_t size = GET_SIZE(HDRP(ptr));

  PUT(HDRP(ptr), PACK(size, 0));
  PUT(FTRP(ptr), PACK(size, 0));
  coalesce(ptr);
}

/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 */
void *mm_realloc(void *bp, size_t size)
{
  if (size <= 0) {
    mm_free(bp);
    return 0;
  }
  if (bp == NULL) {
    return mm_malloc(size);
  }
  void *newp = mm_malloc(size);
  if (newp == NULL) {
    return 0;
  }
  size_t oldsize = GET_SIZE(HDRP(bp));
  if (size < oldsize) {
    oldsize = size;
  }

  memcpy(newp, bp, oldsize);
  mm_free(bp);
  return newp;
}
