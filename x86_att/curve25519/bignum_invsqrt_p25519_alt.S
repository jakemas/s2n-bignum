// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// ----------------------------------------------------------------------------
// Inverse square root modulo p_25519 = 2^255 - 19
// Input x[4]; output function return (Legendre symbol) and z[4]
//
// extern int64_t bignum_invsqrt_p25519_alt(uint64_t z[static 4],
//                                          const uint64_t x[static 4]);
//
// Given a 4-digit input x, returns a modular inverse square root mod p_25519,
// i.e. a z such that x * z^2 == 1 (mod p_25519), whenever one exists. The
// inverse square root z is chosen so that its LSB is even (note that p_25519-z
// is another possibility). The function return is the Legendre/Jacobi symbol
// (x//p_25519), which indicates whether indeed x has a modular inverse square
// root and hence whether the result is meaningful:
//
//   0: x is divisible by p_25519 so trivially there is no inverse square root
//  +1: x is coprime to p_25519 and z is indeed an inverse square root
//  -1: x is coprime to p_25519 but there is no (inverse or direct) square root
//
// Standard x86-64 ABI: RDI = z, RSI = x
// Microsoft x64 ABI:   RCX = z, RDX = x
// ----------------------------------------------------------------------------
#include "_internal_s2n_bignum.h"


        S2N_BN_SYM_VISIBILITY_DIRECTIVE(bignum_invsqrt_p25519_alt)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(bignum_invsqrt_p25519_alt)
        .text

// Size in bytes of a 64-bit word

#define N 8

// Pointer-offset pairs for temporaries on stack

#define a 0(%rsp)
#define b (4*N)(%rsp)
#define s (8*N)(%rsp)
#define t (12*N)(%rsp)
#define u (16*N)(%rsp)
#define res  (20*N)(%rsp)

// Total size to reserve on the stack

#define NSPACE (22*N)

// Corrupted versions when stack is down 8 more

#define u8 (17*N)(%rsp)

// Syntactic variants to make x86_att version simpler to generate

#define A 0
#define B (4*N)
#define S (8*N)
#define T (12*N)
#define U (16*N)
#define U8 (17*N)

S2N_BN_SYMBOL(bignum_invsqrt_p25519_alt):
        _CET_ENDBR

// In this case the Windows form literally makes a subroutine call.
// This avoids hassle arising from subroutine offsets

#if WINDOWS_ABI
        pushq   %rdi
        pushq   %rsi
        movq    %rcx, %rdi
        movq    %rdx, %rsi
        callq   bignum_invsqrt_p25519_alt_standard
        popq    %rsi
        popq    %rdi
        ret

bignum_invsqrt_p25519_alt_standard:
#endif

// Save registers and make room for temporaries

        pushq   %rbx
        pushq   %rbp
        pushq   %r12
        pushq   %r13
        pushq   %r14
        pushq   %r15

        subq    $NSPACE, %rsp

// Save the return pointer for the end so we can overwrite %rdi later

        movq    %rdi, res

// Set up reduced version of the input argument a = x mod p_25519. Then
// get the candidate inverse square root s = a^{252-3}

        movq    (%rsi), %rdx
        movq    0x8(%rsi), %rcx
        movq    0x10(%rsi), %r8
        movq    0x18(%rsi), %r9
        movl    $0x1, %eax
        xorl    %r10d, %r10d
        bts     $0x3f, %r9
        adcq    %r10, %rax
        imulq   $0x13, %rax, %rax
        addq    %rax, %rdx
        adcq    %r10, %rcx
        adcq    %r10, %r8
        adcq    %r10, %r9
        movl    $0x13, %eax
        cmovbq  %r10, %rax
        subq    %rax, %rdx
        sbbq    %r10, %rcx
        sbbq    %r10, %r8
        sbbq    %r10, %r9
        btr     $0x3f, %r9
        movq    %rdx, A(%rsp)
        movq    %rcx, A+0x8(%rsp)
        movq    %r8, A+0x10(%rsp)
        movq    %r9, A+0x18(%rsp)

  // Power 2^2 - 1 = 3

        leaq    T(%rsp), %rdi
        movq    $1, %rsi
        leaq    A(%rsp), %rdx
        callq   bignum_invsqrt_p25519_alt_nsqr_p25519

        leaq    T(%rsp), %rdi
        leaq    T(%rsp), %rsi
        leaq    A(%rsp), %rdx
        callq   bignum_invsqrt_p25519_alt_mul_p25519

  // Power 2^4 - 1 = 15

        leaq    S(%rsp), %rdi
        movq    $2, %rsi
        leaq    T(%rsp), %rdx
        callq   bignum_invsqrt_p25519_alt_nsqr_p25519

        leaq    T(%rsp), %rdi
        leaq    S(%rsp), %rsi
        leaq    T(%rsp), %rdx
        callq   bignum_invsqrt_p25519_alt_mul_p25519

  // Power 2^5 - 1 = 31

        leaq    S(%rsp), %rdi
        movq    $1, %rsi
        leaq    T(%rsp), %rdx
        callq   bignum_invsqrt_p25519_alt_nsqr_p25519

        leaq    B(%rsp), %rdi
        leaq    S(%rsp), %rsi
        leaq    A(%rsp), %rdx
        callq   bignum_invsqrt_p25519_alt_mul_p25519

  // Power 2^10 - 1

        leaq    S(%rsp), %rdi
        movq    $5, %rsi
        leaq    B(%rsp), %rdx
        callq   bignum_invsqrt_p25519_alt_nsqr_p25519

        leaq    T(%rsp), %rdi
        leaq    S(%rsp), %rsi
        leaq    B(%rsp), %rdx
        callq   bignum_invsqrt_p25519_alt_mul_p25519

  // Power 2^20 - 1

        leaq    S(%rsp), %rdi
        movq    $10, %rsi
        leaq    T(%rsp), %rdx
        callq   bignum_invsqrt_p25519_alt_nsqr_p25519

        leaq    T(%rsp), %rdi
        leaq    S(%rsp), %rsi
        leaq    T(%rsp), %rdx
        callq   bignum_invsqrt_p25519_alt_mul_p25519

  // Power 2^25 - 1

        leaq    S(%rsp), %rdi
        movq    $5, %rsi
        leaq    T(%rsp), %rdx
        callq   bignum_invsqrt_p25519_alt_nsqr_p25519

        leaq    B(%rsp), %rdi
        leaq    S(%rsp), %rsi
        leaq    B(%rsp), %rdx
        callq   bignum_invsqrt_p25519_alt_mul_p25519

  // Power 2^50 - 1

        leaq    S(%rsp), %rdi
        movq    $25, %rsi
        leaq    B(%rsp), %rdx
        callq   bignum_invsqrt_p25519_alt_nsqr_p25519

        leaq    T(%rsp), %rdi
        leaq    S(%rsp), %rsi
        leaq    B(%rsp), %rdx
        callq   bignum_invsqrt_p25519_alt_mul_p25519

  // Power 2^100 - 1

        leaq    S(%rsp), %rdi
        movq    $50, %rsi
        leaq    T(%rsp), %rdx
        callq   bignum_invsqrt_p25519_alt_nsqr_p25519

        leaq    T(%rsp), %rdi
        leaq    S(%rsp), %rsi
        leaq    T(%rsp), %rdx
        callq   bignum_invsqrt_p25519_alt_mul_p25519

  // Power 2^125 - 1

        leaq    S(%rsp), %rdi
        movq    $25, %rsi
        leaq    T(%rsp), %rdx
        callq   bignum_invsqrt_p25519_alt_nsqr_p25519

        leaq    B(%rsp), %rdi
        leaq    S(%rsp), %rsi
        leaq    B(%rsp), %rdx
        callq   bignum_invsqrt_p25519_alt_mul_p25519

  // Power 2^250 - 1

        leaq    S(%rsp), %rdi
        movq    $125, %rsi
        leaq    B(%rsp), %rdx
        callq   bignum_invsqrt_p25519_alt_nsqr_p25519

        leaq    B(%rsp), %rdi
        leaq    S(%rsp), %rsi
        leaq    B(%rsp), %rdx
        callq   bignum_invsqrt_p25519_alt_mul_p25519

  // Power 2^252 - 3

        leaq    S(%rsp), %rdi
        movq    $2, %rsi
        leaq    B(%rsp), %rdx
        callq   bignum_invsqrt_p25519_alt_nsqr_p25519

        leaq    S(%rsp), %rdi
        leaq    S(%rsp), %rsi
        leaq    A(%rsp), %rdx
        callq   bignum_invsqrt_p25519_alt_mul_p25519

// s = a^{2^252-3} is now one candidate inverse square root.
// Generate the other one t = s * j_25519 where j_25519 = sqrt(-1)

        movq    $0xc4ee1b274a0ea0b0, %rax
        movq    %rax, T(%rsp)
        movq    $0x2f431806ad2fe478, %rax
        movq    %rax, T+8(%rsp)
        movq    $0x2b4d00993dfbd7a7, %rax
        movq    %rax, T+16(%rsp)
        movq    $0x2b8324804fc1df0b, %rax
        movq    %rax, T+24(%rsp)

        leaq    T(%rsp), %rdi
        leaq    S(%rsp), %rsi
        leaq    T(%rsp), %rdx
        callq   bignum_invsqrt_p25519_alt_mul_p25519

// Now multiplex between them according to whether a * s^2 = 1

        leaq    B(%rsp), %rdi
        movq    $1, %rsi
        leaq    S(%rsp), %rdx
        callq   bignum_invsqrt_p25519_alt_nsqr_p25519

        leaq    B(%rsp), %rdi
        leaq    A(%rsp), %rsi
        leaq    B(%rsp), %rdx
        callq   bignum_invsqrt_p25519_alt_mul_p25519

        movq    B(%rsp), %rax
        xorq    $1, %rax
        movq    B+8(%rsp), %rbx
        orq     %rbx, %rax
        movq    B+16(%rsp), %rcx
        movq    B+24(%rsp), %rdx
        orq     %rdx, %rcx
        orq     %rcx, %rax

        movq    S(%rsp), %rax
        movq    T(%rsp), %rbx
        cmovnzq %rbx, %rax
        movq    S+8(%rsp), %rbx
        movq    T+8(%rsp), %rcx
        cmovnzq %rcx, %rbx
        movq    S+16(%rsp), %rcx
        movq    T+16(%rsp), %rdx
        cmovnzq %rdx, %rcx
        movq    S+24(%rsp), %rbp
        movq    T+24(%rsp), %rdx
        cmovnzq %rdx, %rbp

// For definiteness, choose "positive" (LSB=0) inverse square root

        xorl    %edx, %edx
        leaq    -19(%rdx), %r8
        leaq    -1(%rdx), %r11
        movq    %r11, %r9
        movq    %r11, %r10
        btr     $63, %r11

        subq    %rax, %r8
        sbbq    %rbx, %r9
        sbbq    %rcx, %r10
        sbbq    %rbp, %r11

        movq    res, %rdx
        testq   $1, %rax
        cmovnzq %r8, %rax
        movq    %rax, (%rdx)
        cmovnzq %r9, %rbx
        movq    %rbx, 8(%rdx)
        cmovnzq %r10, %rcx
        movq    %rcx, 16(%rdx)
        cmovnzq %r11, %rbp
        movq    %rbp, 24(%rdx)

// Determine if it is is indeed an inverse square root, also distinguishing
// the degenerate x * z^2 == 0 (mod p_25519) case, which is equivalent to
// x == 0 (mod p_25519). Hence return the Legendre-Jacobi symbol as required.

        leaq    B(%rsp), %rdi
        movq    $1, %rsi
        callq   bignum_invsqrt_p25519_alt_nsqr_p25519

        leaq    B(%rsp), %rdi
        leaq    A(%rsp), %rsi
        leaq    B(%rsp), %rdx
        callq   bignum_invsqrt_p25519_alt_mul_p25519

        movq    $1, %rax
        movq    B(%rsp), %rbp
        xorq    %rbp, %rax
        movq    B+8(%rsp), %rbx
        orq     %rbx, %rax
        orq     %rbx, %rbp
        movq    B+16(%rsp), %rcx
        movq    B+24(%rsp), %rdx
        orq     %rdx, %rcx
        orq     %rcx, %rax
        orq     %rcx, %rbp

        negq    %rax
        sbbq    %rax, %rax
        leaq    1(%rax,%rax,1), %rax

        testq   %rbp, %rbp
        cmovzq  %rbp, %rax

// Restore stack and registers

        addq    $NSPACE, %rsp

        popq    %r15
        popq    %r14
        popq    %r13
        popq    %r12
        popq    %rbp
        popq    %rbx
        ret

// *************************************************************
// Local z = x * y
// *************************************************************

bignum_invsqrt_p25519_alt_mul_p25519:
        movq    %rdx, %rcx
        movq    (%rsi), %rax
        mulq     (%rcx)
        movq    %rax, %r8
        movq    %rdx, %r9
        xorq    %r10, %r10
        xorq    %r11, %r11
        movq    (%rsi), %rax
        mulq     0x8(%rcx)
        addq    %rax, %r9
        adcq    %rdx, %r10
        movq    0x8(%rsi), %rax
        mulq     (%rcx)
        addq    %rax, %r9
        adcq    %rdx, %r10
        adcq    $0x0, %r11
        xorq    %r12, %r12
        movq    (%rsi), %rax
        mulq     0x10(%rcx)
        addq    %rax, %r10
        adcq    %rdx, %r11
        adcq    %r12, %r12
        movq    0x8(%rsi), %rax
        mulq     0x8(%rcx)
        addq    %rax, %r10
        adcq    %rdx, %r11
        adcq    $0x0, %r12
        movq    0x10(%rsi), %rax
        mulq     (%rcx)
        addq    %rax, %r10
        adcq    %rdx, %r11
        adcq    $0x0, %r12
        xorq    %r13, %r13
        movq    (%rsi), %rax
        mulq     0x18(%rcx)
        addq    %rax, %r11
        adcq    %rdx, %r12
        adcq    %r13, %r13
        movq    0x8(%rsi), %rax
        mulq     0x10(%rcx)
        addq    %rax, %r11
        adcq    %rdx, %r12
        adcq    $0x0, %r13
        movq    0x10(%rsi), %rax
        mulq     0x8(%rcx)
        addq    %rax, %r11
        adcq    %rdx, %r12
        adcq    $0x0, %r13
        movq    0x18(%rsi), %rax
        mulq     (%rcx)
        addq    %rax, %r11
        adcq    %rdx, %r12
        adcq    $0x0, %r13
        xorq    %r14, %r14
        movq    0x8(%rsi), %rax
        mulq     0x18(%rcx)
        addq    %rax, %r12
        adcq    %rdx, %r13
        adcq    %r14, %r14
        movq    0x10(%rsi), %rax
        mulq     0x10(%rcx)
        addq    %rax, %r12
        adcq    %rdx, %r13
        adcq    $0x0, %r14
        movq    0x18(%rsi), %rax
        mulq     0x8(%rcx)
        addq    %rax, %r12
        adcq    %rdx, %r13
        adcq    $0x0, %r14
        xorq    %r15, %r15
        movq    0x10(%rsi), %rax
        mulq     0x18(%rcx)
        addq    %rax, %r13
        adcq    %rdx, %r14
        adcq    %r15, %r15
        movq    0x18(%rsi), %rax
        mulq     0x10(%rcx)
        addq    %rax, %r13
        adcq    %rdx, %r14
        adcq    $0x0, %r15
        movq    0x18(%rsi), %rax
        mulq     0x18(%rcx)
        addq    %rax, %r14
        adcq    %rdx, %r15
        movl    $0x26, %esi
        movq    %r12, %rax
        mulq    %rsi
        addq    %rax, %r8
        adcq    %rdx, %r9
        sbbq    %rcx, %rcx
        movq    %r13, %rax
        mulq    %rsi
        subq    %rcx, %rdx
        addq    %rax, %r9
        adcq    %rdx, %r10
        sbbq    %rcx, %rcx
        movq    %r14, %rax
        mulq    %rsi
        subq    %rcx, %rdx
        addq    %rax, %r10
        adcq    %rdx, %r11
        sbbq    %rcx, %rcx
        movq    %r15, %rax
        mulq    %rsi
        subq    %rcx, %rdx
        xorq    %rcx, %rcx
        addq    %rax, %r11
        movq    %rdx, %r12
        adcq    %rcx, %r12
        shldq   $0x1, %r11, %r12
        leaq    0x1(%r12), %rax
        movl    $0x13, %esi
        bts     $0x3f, %r11
        imulq   %rsi, %rax
        addq    %rax, %r8
        adcq    %rcx, %r9
        adcq    %rcx, %r10
        adcq    %rcx, %r11
        sbbq    %rax, %rax
        notq    %rax
        andq    %rsi, %rax
        subq    %rax, %r8
        sbbq    %rcx, %r9
        sbbq    %rcx, %r10
        sbbq    %rcx, %r11
        btr     $0x3f, %r11
        movq    %r8, (%rdi)
        movq    %r9, 0x8(%rdi)
        movq    %r10, 0x10(%rdi)
        movq    %r11, 0x18(%rdi)
        ret

// *************************************************************
// Local z = 2^n * x
// *************************************************************

bignum_invsqrt_p25519_alt_nsqr_p25519:

// Copy input argument into u

        movq    (%rdx), %rax
        movq    8(%rdx), %rbx
        movq    16(%rdx), %rcx
        movq    24(%rdx), %rdx
        movq    %rax, U8(%rsp)
        movq    %rbx, U8+8(%rsp)
        movq    %rcx, U8+16(%rsp)
        movq    %rdx, U8+24(%rsp)

// Main squaring loop, accumulating in u consistently  and
// only ensuring the intermediates are < 2 * p_25519 = 2^256 - 38

bignum_invsqrt_p25519_alt_loop:
        movq    U8(%rsp), %rax
        mulq    %rax
        movq    %rax, %r8
        movq    %rdx, %r9
        xorq    %r10, %r10
        xorq    %r11, %r11
        movq    U8(%rsp), %rax
        mulq     U8+0x8(%rsp)
        addq    %rax, %rax
        adcq    %rdx, %rdx
        adcq    $0x0, %r11
        addq    %rax, %r9
        adcq    %rdx, %r10
        adcq    $0x0, %r11
        xorq    %r12, %r12
        movq    U8+0x8(%rsp), %rax
        mulq    %rax
        addq    %rax, %r10
        adcq    %rdx, %r11
        adcq    $0x0, %r12
        movq    U8(%rsp), %rax
        mulq     U8+0x10(%rsp)
        addq    %rax, %rax
        adcq    %rdx, %rdx
        adcq    $0x0, %r12
        addq    %rax, %r10
        adcq    %rdx, %r11
        adcq    $0x0, %r12
        xorq    %r13, %r13
        movq    U8(%rsp), %rax
        mulq     U8+0x18(%rsp)
        addq    %rax, %rax
        adcq    %rdx, %rdx
        adcq    $0x0, %r13
        addq    %rax, %r11
        adcq    %rdx, %r12
        adcq    $0x0, %r13
        movq    U8+0x8(%rsp), %rax
        mulq     U8+0x10(%rsp)
        addq    %rax, %rax
        adcq    %rdx, %rdx
        adcq    $0x0, %r13
        addq    %rax, %r11
        adcq    %rdx, %r12
        adcq    $0x0, %r13
        xorq    %r14, %r14
        movq    U8+0x8(%rsp), %rax
        mulq     U8+0x18(%rsp)
        addq    %rax, %rax
        adcq    %rdx, %rdx
        adcq    $0x0, %r14
        addq    %rax, %r12
        adcq    %rdx, %r13
        adcq    $0x0, %r14
        movq    U8+0x10(%rsp), %rax
        mulq    %rax
        addq    %rax, %r12
        adcq    %rdx, %r13
        adcq    $0x0, %r14
        xorq    %r15, %r15
        movq    U8+0x10(%rsp), %rax
        mulq     U8+0x18(%rsp)
        addq    %rax, %rax
        adcq    %rdx, %rdx
        adcq    $0x0, %r15
        addq    %rax, %r13
        adcq    %rdx, %r14
        adcq    $0x0, %r15
        movq    U8+0x18(%rsp), %rax
        mulq    %rax
        addq    %rax, %r14
        adcq    %rdx, %r15
        movl    $0x26, %ebx
        movq    %r12, %rax
        mulq    %rbx
        addq    %rax, %r8
        adcq    %rdx, %r9
        sbbq    %rcx, %rcx
        movq    %r13, %rax
        mulq    %rbx
        subq    %rcx, %rdx
        addq    %rax, %r9
        adcq    %rdx, %r10
        sbbq    %rcx, %rcx
        movq    %r14, %rax
        mulq    %rbx
        subq    %rcx, %rdx
        addq    %rax, %r10
        adcq    %rdx, %r11
        sbbq    %rcx, %rcx
        movq    %r15, %rax
        mulq    %rbx
        subq    %rcx, %rdx
        xorq    %rcx, %rcx
        addq    %rax, %r11
        movq    %rdx, %r12
        adcq    %rcx, %r12
        shldq   $0x1, %r11, %r12
        btr     $0x3f, %r11
        movl    $0x13, %edx
        imulq   %r12, %rdx
        addq    %rdx, %r8
        adcq    %rcx, %r9
        adcq    %rcx, %r10
        adcq    %rcx, %r11
        movq    %r8, U8(%rsp)
        movq    %r9, U8+0x8(%rsp)
        movq    %r10, U8+0x10(%rsp)
        movq    %r11, U8+0x18(%rsp)

// Loop as applicable

        decq    %rsi
        jnz     bignum_invsqrt_p25519_alt_loop

// We know the intermediate result x < 2^256 - 38, and now we do strict
// modular reduction mod 2^255 - 19. Note x < 2^255 - 19 <=> x + 19 < 2^255
// which is equivalent to a "ns" condition. We just use the results where
// they were in registers [%r11;%r10;%r9;%r8] instead of re-loading them.

        movl    $19, %eax
        xorl    %ebx, %ebx
        xorl    %ecx, %ecx
        xorl    %edx, %edx
        addq    %r8, %rax
        adcq    %r9, %rbx
        adcq    %r10, %rcx
        adcq    %r11, %rdx

        cmovns  %r8, %rax
        cmovns  %r9, %rbx
        cmovns  %r10, %rcx
        cmovns  %r11, %rdx
        btr     $63, %rdx
        movq    %rax, (%rdi)
        movq    %rbx, 8(%rdi)
        movq    %rcx, 16(%rdi)
        movq    %rdx, 24(%rdi)
        ret

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack, "", %progbits
#endif
