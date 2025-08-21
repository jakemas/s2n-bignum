// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// ----------------------------------------------------------------------------
// Canonical reduction of polynomial coefficients for ML-DSA
// Input a[256] (signed 32-bit words); output a[256] (signed 32-bit words)
//
// This reduces each element of the 256-element array of 32-bit signed
// integers modulo 8380417 with the result being centered around zero,
// specifically -6283009 <= r <= 6283008, in-place.
// This is intended for use when that array represents polynomial
// coefficients for ML-DSA, but that is not relevant to its operation.
//
// extern void mldsa_poly_reduce(int32_t a[256]);
//
// Standard x86_64 ABI: RDI = a
// ----------------------------------------------------------------------------
#include "_internal_s2n_bignum.h"

        .intel_syntax noprefix
        S2N_BN_SYM_VISIBILITY_DIRECTIVE(mldsa_poly_reduce)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(mldsa_poly_reduce)
        .text

#define a rdi
#define offset rax
#define count rcx

S2N_BN_SYMBOL(mldsa_poly_reduce):

// Written and derived from the public domain AVX2 Dilithium 
// implementation and matches the mldsa-native poly_reduce_avx2 function

// Load constants using inline approach
        mov     eax, 8380417
        movd    xmm0, eax
        vpbroadcastd ymm0, xmm0                   // q in all lanes
        
        mov     eax, 4194304                      // 1 << 22
        movd    xmm1, eax
        vpbroadcastd ymm1, xmm1                   // offset in all lanes
        
// Setup loop counter
        xor     offset, offset                    // byte offset = 0
        mov     count, 1024                       // Total bytes (MLDSA_N * sizeof(int32_t))
        
mldsa_poly_reduce_loop:
// Load 8 int32_t values
        vmovdqa ymm2, [a+offset]                  // f = _mm256_load_si256(&rr[i])
        
// Perform reduction
        vpaddd  ymm3, ymm2, ymm1                  // g = f + offset
        vpsrad  ymm3, ymm3, 23                    // g = g >> 23
        
// Multiply by q using vpmulld
        vpmulld ymm3, ymm3, ymm0                  // g = g * q
        
// Subtract from original value
        vpsubd  ymm2, ymm2, ymm3                  // f = f - g
        
// Store result
        vmovdqa [a+offset], ymm2                  // _mm256_store_si256(&rr[i], f)
        
// Increment counter and check loop condition
        add     offset, 32                        // Move to next 32 bytes (8 int32_t values)
        cmp     offset, count                     // Compare with total bytes
        jb      mldsa_poly_reduce_loop
        
// Return
        ret

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif
