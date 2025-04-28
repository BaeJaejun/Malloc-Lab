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
    "ateam",
    /* First member's full name */
    "Harry Bovik",
    /* First member's email address */
    "bovik@cs.cmu.edu",
    /* Second member's full name (leave blank if none) */
    "",
    /* Second member's email address (leave blank if none) */
    ""};

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT - 1)) & ~0x7)

#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

// 가용리스트 조작 매크로
// 워드 및 더블 워드 크기 정의
#define WSIZE       4           // 워드 크기(바이트). 헤더와 풋터의 크기 단위
#define DSIZE       8           // 더블 워드 크기. 블록의 최소 크기 및 정렬 기준
#define CHUNKSIZE   (1 << 12)   // 힙 확장 시 요청할 기본 크기(4KB)

// 유틸리티 매크로
#define MAX(x, y)      ((x) > (y) ? (x) : (y))      // 두 값 중 최대값 반환
#define PACK(size, alloc)  ((size) | (alloc))       // 크기와 할당 비트를 하나의 워드로 결합

// 메모리 접근 매크로
#define GET(p)         (*(unsigned int *)(p))       // 주소 p에서 4바이트 워드 읽기
#define PUT(p, val)    (*(unsigned int *)(p) = (val))// 주소 p에 4바이트 워드 저장

// 헤더/푸터 워드에서 크기 및 할당 정보 추출
#define GET_SIZE(p)    (GET(p) & ~0x7)               // 워드에서 하위 3비트를 제외한 크기 정보
#define GET_ALLOC(p)   (GET(p) & 0x1)               // 워드에서 최하위 비트(할당 여부) 추출

// 블록 포인터(bp)를 기준으로 헤더와 풋터 위치 계산
#define HDRP(bp)       ((char *)(bp) - WSIZE)       // 블록 유효 영역 시작(bp)에서 헤더 시작 위치
#define FTRP(bp)       ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)  
                                                     // 블록 크기만큼 이동한 후 풋터 시작 위치

// 다음·이전 블록의 블록 포인터 계산
#define NEXT_BLKP(bp)  ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))
                                                     // 현재 블록 끝에서 다음 블록의 유효 영역 시작 위치
#define PREV_BLKP(bp)  ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))
                                                     // 현재 블록 헤더 바로 전에서 이전 블록의 유효 영역 시작 위치

/* 힙 리스트 시작점을 가리키는 단 하나의 전역 변수 */
static char *heap_listp;

/* extend_heap 새 가용 블록으로 힙 확장하기*/
static void *extend_heap(size_t words);
/* 인접 가용 블록들과 통합하기*/
static void *coalesce(void *bp);
/* 순회하면서 맞는첫번째 블록 찾기*/
static void *find_fit(size_t asize);
/* 분할 및 헤더,풋터 세팅*/
static void place(void *bp, size_t asize);


/*
 * mm_init - initialize the malloc package.
 */
int mm_init(void)
{
    // 힙 초기 영역 4워드 확보
    if ((heap_listp = mem_sbrk(4*WSIZE)) == (void *)-1)
        return -1;

    PUT(heap_listp, 0);                         // 정렬 패딩 4바이트
    PUT(heap_listp + (1*WSIZE), PACK(DSIZE, 1));// 프롤로그 헤더 
    PUT(heap_listp + (2*WSIZE), PACK(DSIZE, 1));// 프롤로그 푸터
    PUT(heap_listp + (3*WSIZE), PACK(0, 1));    // 에필로그 헤더
    heap_listp += (2*WSIZE); //실제 데이터 블록 시작점으로 이동

    //초기 자유 블록 확보: CHUNKSIZE 만큼 힙 확장 -> 4096/4 = 1024 워드를 요청
    if (extend_heap(CHUNKSIZE/WSIZE) == NULL)
        return -1;
    return 0;
}

static void *extend_heap(size_t words)
{
    char * bp;
    size_t size;
    
    //요청 단위(워드)를 2워드(8바이트)로 맞춰준다.
    size = (words % 2)? (words+1) * WSIZE : words * WSIZE;
    if((long)(bp = mem_sbrk(size)) == -1) // size만큼 힙 확장
        return NULL;

    //확보한 영역을 하나의 자유블록으로 초기화
    PUT(HDRP(bp),PACK(size, 0)); // 헤더 
    PUT(FTRP(bp),PACK(size, 0)); // 푸터
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1)); // 에필로그 헤더 밀어주기

    //이전 블록이 자유 블록이면 병합하여 더 큰 자유 블록으로 변환
    return coalesce(bp);
}

// 병합 함수
static void *coalesce(void *bp)
{   
    // 이웃 블록의 할당 상태를 조회
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));

    // case 1) 이전 / 이후 모두 할당 상태 -> 병합 불필요
    if (prev_alloc && next_alloc){
        return bp;
    }

    // case 2) 이전 할당 / 이후 자유 -> 현재 + 이후 병합
    else if (prev_alloc && !next_alloc){
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
    }

    // case 3) 이전 자유 / 이후 할당 -> 이전 + 현재 병합
    else if (!prev_alloc && next_alloc){
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        PUT(FTRP(bp), PACK(size, 0));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }

    // case 4) 이전 / 이후 모두 자유 -> 이전 + 현재 + 이후 모두 병합
    else {
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(FTRP(NEXT_BLKP(bp)));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }
    return bp;
}
/*
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 */
/* Bump Pointer 방식*/
// void *mm_malloc(size_t size)
// {
//     int newsize = ALIGN(size + SIZE_T_SIZE);
//     void *p = mem_sbrk(newsize);
//     if (p == (void *)-1)
//         return NULL;
//     else
//     {
//         *(size_t *)p = size;
//         return (void *)((char *)p + SIZE_T_SIZE);
//     }
// }

void *mm_malloc(size_t size)
{
    size_t asize; //조정된 블록 크기
    size_t extendsize; // 힙 확장 크기
    char *bp;

    // 0바이트 요청은 무시
    if (size == 0) 
        return NULL;
    
    //할당 크기 조정(헤더,풋터 만큼) 8바이트 단위 반올림
    if (size <= DSIZE)
        asize = 2 * DSIZE;
    else
        //C에서는 나머지를 버림 (DSIZE - 1)을 해줌으로 **올림** 효과
        asize = DSIZE * ((size + DSIZE + (DSIZE - 1)) / DSIZE);
    
    // 묵시적 가용 리스트에서 first-fit 탐색
    if ((bp = find_fit(asize)) != NULL)
    {
        place(bp, asize); //분할 및 블록 할당
        return bp;
    }

    //맞는 블록이 없다면? -> 힙 자체를 확장
    //최소 asize 바이트 만큼 or CHUNKSIZE(4KB) 중 큰 쪽으로 확장
    //시스템 콜(실제 sbrk/mmap 호출)은 비용이 크기 때문에
    //여러 번 작은 단위로 호출하지 않고 한 번에 크게(4KB) 확보
    extendsize = MAX(asize,CHUNKSIZE);

    // 힙 확장: extend_heap에 워드 단위로 넘기기 위해 WSIZE로 나눔
    if ((bp = extend_heap(extendsize/WSIZE)) == NULL)
        return NULL;
    
    // 확장 영역에서 분할 및 블록 할당
    place(bp, asize);
    return bp;
}

static void *find_fit(size_t asize)
{
    /* first- fit */
    void *bp;

    for (bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)){
        if (!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp)))){
            return bp;
        }
    }


    /* No fit */
    return NULL;
}

static void place(void *bp, size_t asize)
{
    size_t csize = GET_SIZE(HDRP(bp)); // 가용 블록의 전체 크기

    // 여분이 2 * DSIZE 이상이면 분할 
    if ((csize - asize) >= (2 * DSIZE))
    {
        PUT(HDRP(bp), PACK(asize, 1));
        PUT(FTRP(bp), PACK(asize, 1));
        bp = NEXT_BLKP(bp);
        PUT(HDRP(bp), PACK(csize - asize, 0));
        PUT(FTRP(bp), PACK(csize - asize, 0));
    }
    // 여분이 없으면 통째로 할당
    else
    {
        PUT(HDRP(bp), PACK(csize, 1));
        PUT(FTRP(bp), PACK(csize, 1));
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
void *mm_realloc(void *ptr, size_t size)
{   
    // realloc(NULL, size) == malloc(size)
    if (ptr == NULL)
        return mm_malloc(size);

    // size 0이면 그냥 할당 해제
    if (size == 0){
        mm_free(ptr);
        return NULL;
    }

    void *oldptr = ptr; // 원본 포인터
    void *newptr;       // 새 포인터
    size_t copySize;

    newptr = mm_malloc(size); // size 만큼 새 포인터에 할당
    if (newptr == NULL)
        return NULL;

    //원본 블록의 요청된 페이로드 크기 읽어오기
    copySize = GET_SIZE(HDRP(ptr)) - DSIZE;
    //실제로 복사할 바이트 수를 결정
    if (size < copySize)
        copySize = size;

    //newptr에 oldptr의 내용을 copysize만큼 복사하기
    memcpy(newptr, oldptr, copySize);

    //원본 할당 해제
    mm_free(oldptr);
    return newptr;
}