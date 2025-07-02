/*
 * Copyright (c) The mldsa-native project authors
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT
 */

/*
 * This file is derived from the public domain
 * AVX2 Dilithium implementation @[REF_AVX2].
 */

#include "../../include/_internal_s2n_bignum.h"

/* Define MLDSA constants */
#define MLDSA_Q 8380417
#define MLDSA_N 256

.text
.balign 16                                      /* Ensure 16-byte alignment for AVX2 code */
.global S2N_BN_SYMBOL(poly_reduce_avx2)
S2N_BN_SYM_VISIBILITY_DIRECTIVE(poly_reduce_avx2)
S2N_BN_SYM_PRIVACY_DIRECTIVE(poly_reduce_avx2)
_CET_ENDBR
S2N_BN_SYMBOL(poly_reduce_avx2):
    /* Load constants directly into registers */
    mov             $MLDSA_Q, %eax              /* q */
    vmovd           %eax, %xmm0                 /* Move q to xmm0 */
    vpbroadcastd    %xmm0, %ymm0                /* Broadcast q to all lanes */
    
    mov             $(1 << 22), %eax            /* offset (1 << 22) */
    vmovd           %eax, %xmm1                 /* Move offset to xmm1 */
    vpbroadcastd    %xmm1, %ymm1                /* Broadcast offset to all lanes */
    
    /* Setup loop counter */
    xor             %rax, %rax                  /* byte offset = 0 */
    mov             $MLDSA_N*4, %rcx            /* Total bytes to process (MLDSA_N * sizeof(int32_t)) */
    
.Lloop:
    /* Load 8 int32_t values */
    vmovdqa         (%rdi,%rax), %ymm2          /* f = _mm256_load_si256(&rr[i]) */
    
    /* Perform reduction */
    vpaddd          %ymm1, %ymm2, %ymm3         /* g = f + offset */
    vpsrad          $23, %ymm3, %ymm3           /* g = g >> 23 */
    
    /* Multiply by q using vpmulld */
    vpmulld         %ymm0, %ymm3, %ymm3         /* g = g * q */
    
    /* Subtract from original value */
    vpsubd          %ymm3, %ymm2, %ymm2         /* f = f - g */
    
    /* Store result */
    vmovdqa         %ymm2, (%rdi,%rax)          /* _mm256_store_si256(&rr[i], f) */
    
    /* Increment counter and check loop condition */
    add             $32, %rax                   /* Move to next 32 bytes (8 int32_t values) */
    cmp             %rcx, %rax                  /* Compare with total bytes */
    jb              .Lloop
    
    /* Return */
    ret
