// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// ----------------------------------------------------------------------------
// Projective scalar multiplication, x coordinate only, for curve25519
// Inputs scalar[4], point[4]; output res[8]
//
// extern void curve25519_pxscalarmul
//   (uint64_t res[static 8],const uint64_t scalar[static 4],
//    const uint64_t point[static 4]);
//
// Given the X coordinate of an input point = (X,Y) on curve25519, which
// could also be part of a projective representation (X,Y,1) of the same
// point, returns a projective representation (X,Z) = scalar * point, where
// scalar is a 256-bit number. The corresponding affine form is (X/Z,Y'),
// X/Z meaning division modulo 2^255-19, and Y' not being computed by
// this function (nor is any Y coordinate of the input point used).
//
// Standard x86-64 ABI: RDI = res, RSI = scalar, RDX = point
// Microsoft x64 ABI:   RCX = res, RDX = scalar, R8 = point
// ----------------------------------------------------------------------------
#include "_internal_s2n_bignum.h"


        S2N_BN_SYM_VISIBILITY_DIRECTIVE(curve25519_pxscalarmul)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(curve25519_pxscalarmul)
        .text

// Size of individual field elements

#define NUMSIZE 32

// Stable homes for input arguments during main code sequence
// and additional registers for loop counter and swap flag

#define res  10*NUMSIZE(%rsp)
#define point  10*NUMSIZE+8(%rsp)
#define scalar  10*NUMSIZE+16(%rsp)
#define i  10*NUMSIZE+24(%rsp)
#define swap  10*NUMSIZE+32(%rsp)

// Pointers to input x coord (we don't use y or z) and output coords.
// These all assume the base address (point and res respectively) is
// currently in the %rbp register.

#define x 0(%rbp)
#define resx 0(%rbp)
#define resz NUMSIZE(%rbp)

// Pointer-offset pairs for temporaries on stack with some aliasing.
// Both dmsn and dnsm need space for >= 5 digits, and we allocate 8

#define zm (0*NUMSIZE)(%rsp)
#define sm (0*NUMSIZE)(%rsp)
#define dpro (0*NUMSIZE)(%rsp)

#define sn (1*NUMSIZE)(%rsp)

#define dm (2*NUMSIZE)(%rsp)

#define zn (3*NUMSIZE)(%rsp)
#define dn (3*NUMSIZE)(%rsp)
#define e (3*NUMSIZE)(%rsp)

#define dmsn (4*NUMSIZE)(%rsp)
#define p (4*NUMSIZE)(%rsp)

#define xm (6*NUMSIZE)(%rsp)
#define dnsm (6*NUMSIZE)(%rsp)
#define spro (6*NUMSIZE)(%rsp)

#define xn (8*NUMSIZE)(%rsp)
#define s (8*NUMSIZE)(%rsp)

#define d (9*NUMSIZE)(%rsp)

// Total size to reserve on the stack
// This includes space for the 5 other variables above

#define NSPACE (10*NUMSIZE+40)

// Macros wrapping up the basic field operation calls
// bignum_mul_p25519 and bignum_sqr_p25519.
// These two are only trivially different from pure
// function calls to those subroutines.

#define mul_p25519(P0,P1,P2)                    \
        xorl   %edi, %edi ;                        \
        movq   P2, %rdx ;                       \
        mulxq  P1, %r8, %r9 ;                    \
        mulxq  0x8+P1, %rax, %r10 ;              \
        addq   %rax, %r9 ;                         \
        mulxq  0x10+P1, %rax, %r11 ;             \
        adcq   %rax, %r10 ;                        \
        mulxq  0x18+P1, %rax, %r12 ;             \
        adcq   %rax, %r11 ;                        \
        adcq   %rdi, %r12 ;                        \
        xorl   %edi, %edi ;                        \
        movq   0x8+P2, %rdx ;                   \
        mulxq  P1, %rax, %rbx ;                  \
        adcxq  %rax, %r9 ;                         \
        adoxq  %rbx, %r10 ;                        \
        mulxq  0x8+P1, %rax, %rbx ;              \
        adcxq  %rax, %r10 ;                        \
        adoxq  %rbx, %r11 ;                        \
        mulxq  0x10+P1, %rax, %rbx ;             \
        adcxq  %rax, %r11 ;                        \
        adoxq  %rbx, %r12 ;                        \
        mulxq  0x18+P1, %rax, %r13 ;             \
        adcxq  %rax, %r12 ;                        \
        adoxq  %rdi, %r13 ;                        \
        adcxq  %rdi, %r13 ;                        \
        xorl   %edi, %edi ;                        \
        movq   0x10+P2, %rdx ;                  \
        mulxq  P1, %rax, %rbx ;                  \
        adcxq  %rax, %r10 ;                        \
        adoxq  %rbx, %r11 ;                        \
        mulxq  0x8+P1, %rax, %rbx ;              \
        adcxq  %rax, %r11 ;                        \
        adoxq  %rbx, %r12 ;                        \
        mulxq  0x10+P1, %rax, %rbx ;             \
        adcxq  %rax, %r12 ;                        \
        adoxq  %rbx, %r13 ;                        \
        mulxq  0x18+P1, %rax, %r14 ;             \
        adcxq  %rax, %r13 ;                        \
        adoxq  %rdi, %r14 ;                        \
        adcxq  %rdi, %r14 ;                        \
        xorl   %edi, %edi ;                        \
        movq   0x18+P2, %rdx ;                  \
        mulxq  P1, %rax, %rbx ;                  \
        adcxq  %rax, %r11 ;                        \
        adoxq  %rbx, %r12 ;                        \
        mulxq  0x8+P1, %rax, %rbx ;              \
        adcxq  %rax, %r12 ;                        \
        adoxq  %rbx, %r13 ;                        \
        mulxq  0x10+P1, %rax, %rbx ;             \
        adcxq  %rax, %r13 ;                        \
        adoxq  %rbx, %r14 ;                        \
        mulxq  0x18+P1, %rax, %r15 ;             \
        adcxq  %rax, %r14 ;                        \
        adoxq  %rdi, %r15 ;                        \
        adcxq  %rdi, %r15 ;                        \
        movl   $0x26, %edx ;                       \
        xorl   %edi, %edi ;                        \
        mulxq  %r12, %rax, %rbx ;                   \
        adcxq  %rax, %r8 ;                         \
        adoxq  %rbx, %r9 ;                         \
        mulxq  %r13, %rax, %rbx ;                   \
        adcxq  %rax, %r9 ;                         \
        adoxq  %rbx, %r10 ;                        \
        mulxq  %r14, %rax, %rbx ;                   \
        adcxq  %rax, %r10 ;                        \
        adoxq  %rbx, %r11 ;                        \
        mulxq  %r15, %rax, %r12 ;                   \
        adcxq  %rax, %r11 ;                        \
        adoxq  %rdi, %r12 ;                        \
        adcxq  %rdi, %r12 ;                        \
        shldq  $0x1, %r11, %r12 ;                   \
        movl   $0x13, %edx ;                       \
        incq   %r12;                             \
        bts    $63, %r11 ;                         \
        mulxq  %r12, %rax, %rbx ;                   \
        addq   %rax, %r8 ;                         \
        adcq   %rbx, %r9 ;                         \
        adcq   %rdi, %r10 ;                        \
        adcq   %rdi, %r11 ;                        \
        sbbq   %rax, %rax ;                        \
        notq   %rax;                             \
        andq   %rdx, %rax ;                        \
        subq   %rax, %r8 ;                         \
        sbbq   %rdi, %r9 ;                         \
        sbbq   %rdi, %r10 ;                        \
        sbbq   %rdi, %r11 ;                        \
        btr    $63, %r11 ;                         \
        movq   %r8, P0 ;                        \
        movq   %r9, 0x8+P0 ;                    \
        movq   %r10, 0x10+P0 ;                  \
        movq   %r11, 0x18+P0

#define sqr_p25519(P0,P1)                       \
        movq   P1, %rdx ;                       \
        mulxq  %rdx, %r8, %r15 ;                    \
        mulxq  0x8+P1, %r9, %r10 ;               \
        mulxq  0x18+P1, %r11, %r12 ;             \
        movq   0x10+P1, %rdx ;                  \
        mulxq  0x18+P1, %r13, %r14 ;             \
        xorl   %ebx, %ebx ;                        \
        mulxq  P1, %rax, %rcx ;                  \
        adcxq  %rax, %r10 ;                        \
        adoxq  %rcx, %r11 ;                        \
        mulxq  0x8+P1, %rax, %rcx ;              \
        adcxq  %rax, %r11 ;                        \
        adoxq  %rcx, %r12 ;                        \
        movq   0x18+P1, %rdx ;                  \
        mulxq  0x8+P1, %rax, %rcx ;              \
        adcxq  %rax, %r12 ;                        \
        adoxq  %rcx, %r13 ;                        \
        adcxq  %rbx, %r13 ;                        \
        adoxq  %rbx, %r14 ;                        \
        adcq   %rbx, %r14 ;                        \
        xorl   %ebx, %ebx ;                        \
        adcxq  %r9, %r9 ;                          \
        adoxq  %r15, %r9 ;                         \
        movq   0x8+P1, %rdx ;                   \
        mulxq  %rdx, %rax, %rdx ;                   \
        adcxq  %r10, %r10 ;                        \
        adoxq  %rax, %r10 ;                        \
        adcxq  %r11, %r11 ;                        \
        adoxq  %rdx, %r11 ;                        \
        movq   0x10+P1, %rdx ;                  \
        mulxq  %rdx, %rax, %rdx ;                   \
        adcxq  %r12, %r12 ;                        \
        adoxq  %rax, %r12 ;                        \
        adcxq  %r13, %r13 ;                        \
        adoxq  %rdx, %r13 ;                        \
        movq   0x18+P1, %rdx ;                  \
        mulxq  %rdx, %rax, %r15 ;                   \
        adcxq  %r14, %r14 ;                        \
        adoxq  %rax, %r14 ;                        \
        adcxq  %rbx, %r15 ;                        \
        adoxq  %rbx, %r15 ;                        \
        movl   $0x26, %edx ;                       \
        xorl   %ebx, %ebx ;                        \
        mulxq  %r12, %rax, %rcx ;                   \
        adcxq  %rax, %r8 ;                         \
        adoxq  %rcx, %r9 ;                         \
        mulxq  %r13, %rax, %rcx ;                   \
        adcxq  %rax, %r9 ;                         \
        adoxq  %rcx, %r10 ;                        \
        mulxq  %r14, %rax, %rcx ;                   \
        adcxq  %rax, %r10 ;                        \
        adoxq  %rcx, %r11 ;                        \
        mulxq  %r15, %rax, %r12 ;                   \
        adcxq  %rax, %r11 ;                        \
        adoxq  %rbx, %r12 ;                        \
        adcxq  %rbx, %r12 ;                        \
        shldq  $0x1, %r11, %r12 ;                   \
        movl   $0x13, %edx ;                       \
        leaq   0x1(%r12), %rax ;                  \
        bts    $0x3f, %r11 ;                       \
        imulq  %rdx, %rax ;                        \
        addq   %rax, %r8 ;                         \
        adcq   %rbx, %r9 ;                         \
        adcq   %rbx, %r10 ;                        \
        adcq   %rbx, %r11 ;                        \
        cmovbq %rbx, %rdx ;                        \
        subq   %rdx, %r8 ;                         \
        sbbq   %rbx, %r9 ;                         \
        sbbq   %rbx, %r10 ;                        \
        sbbq   %rbx, %r11 ;                        \
        btr    $0x3f, %r11 ;                       \
        movq   %r8, P0 ;                        \
        movq   %r9, 0x8+P0 ;                    \
        movq   %r10, 0x10+P0 ;                  \
        movq   %r11, 0x18+P0

// Multiplication just giving a 5-digit result (actually < 39 * p_25519)
// by not doing anything beyond the first stage of reduction

#define mul_5(P0,P1,P2)                         \
        xorl   %edi, %edi ;                        \
        movq   P2, %rdx ;                       \
        mulxq  P1, %r8, %r9 ;                    \
        mulxq  0x8+P1, %rax, %r10 ;              \
        addq   %rax, %r9 ;                         \
        mulxq  0x10+P1, %rax, %r11 ;             \
        adcq   %rax, %r10 ;                        \
        mulxq  0x18+P1, %rax, %r12 ;             \
        adcq   %rax, %r11 ;                        \
        adcq   %rdi, %r12 ;                        \
        xorl   %edi, %edi ;                        \
        movq   0x8+P2, %rdx ;                   \
        mulxq  P1, %rax, %rbx ;                  \
        adcxq  %rax, %r9 ;                         \
        adoxq  %rbx, %r10 ;                        \
        mulxq  0x8+P1, %rax, %rbx ;              \
        adcxq  %rax, %r10 ;                        \
        adoxq  %rbx, %r11 ;                        \
        mulxq  0x10+P1, %rax, %rbx ;             \
        adcxq  %rax, %r11 ;                        \
        adoxq  %rbx, %r12 ;                        \
        mulxq  0x18+P1, %rax, %r13 ;             \
        adcxq  %rax, %r12 ;                        \
        adoxq  %rdi, %r13 ;                        \
        adcxq  %rdi, %r13 ;                        \
        xorl   %edi, %edi ;                        \
        movq   0x10+P2, %rdx ;                  \
        mulxq  P1, %rax, %rbx ;                  \
        adcxq  %rax, %r10 ;                        \
        adoxq  %rbx, %r11 ;                        \
        mulxq  0x8+P1, %rax, %rbx ;              \
        adcxq  %rax, %r11 ;                        \
        adoxq  %rbx, %r12 ;                        \
        mulxq  0x10+P1, %rax, %rbx ;             \
        adcxq  %rax, %r12 ;                        \
        adoxq  %rbx, %r13 ;                        \
        mulxq  0x18+P1, %rax, %r14 ;             \
        adcxq  %rax, %r13 ;                        \
        adoxq  %rdi, %r14 ;                        \
        adcxq  %rdi, %r14 ;                        \
        xorl   %edi, %edi ;                        \
        movq   0x18+P2, %rdx ;                  \
        mulxq  P1, %rax, %rbx ;                  \
        adcxq  %rax, %r11 ;                        \
        adoxq  %rbx, %r12 ;                        \
        mulxq  0x8+P1, %rax, %rbx ;              \
        adcxq  %rax, %r12 ;                        \
        adoxq  %rbx, %r13 ;                        \
        mulxq  0x10+P1, %rax, %rbx ;             \
        adcxq  %rax, %r13 ;                        \
        adoxq  %rbx, %r14 ;                        \
        mulxq  0x18+P1, %rax, %r15 ;             \
        adcxq  %rax, %r14 ;                        \
        adoxq  %rdi, %r15 ;                        \
        adcxq  %rdi, %r15 ;                        \
        movl   $0x26, %edx ;                       \
        xorl   %edi, %edi ;                        \
        mulxq  %r12, %rax, %rbx ;                   \
        adcxq  %rax, %r8 ;                         \
        adoxq  %rbx, %r9 ;                         \
        mulxq  %r13, %rax, %rbx ;                   \
        adcxq  %rax, %r9 ;                         \
        adoxq  %rbx, %r10 ;                        \
        mulxq  %r14, %rax, %rbx ;                   \
        adcxq  %rax, %r10 ;                        \
        adoxq  %rbx, %r11 ;                        \
        mulxq  %r15, %rax, %r12 ;                   \
        adcxq  %rax, %r11 ;                        \
        adoxq  %rdi, %r12 ;                        \
        adcxq  %rdi, %r12 ;                        \
        movq   %r8, P0 ;                        \
        movq   %r9, 0x8+P0 ;                    \
        movq   %r10, 0x10+P0 ;                  \
        movq   %r11, 0x18+P0 ;                  \
        movq   %r12, 0x20+P0

// Squaring just giving a result < 2 * p_25519, which is done by
// basically skipping the +1 in the quotient estimate and the final
// optional correction.

#define sqr_4(P0,P1)                            \
        movq   P1, %rdx ;                       \
        mulxq  %rdx, %r8, %r15 ;                    \
        mulxq  0x8+P1, %r9, %r10 ;               \
        mulxq  0x18+P1, %r11, %r12 ;             \
        movq   0x10+P1, %rdx ;                  \
        mulxq  0x18+P1, %r13, %r14 ;             \
        xorl   %ebx, %ebx ;                        \
        mulxq  P1, %rax, %rcx ;                  \
        adcxq  %rax, %r10 ;                        \
        adoxq  %rcx, %r11 ;                        \
        mulxq  0x8+P1, %rax, %rcx ;              \
        adcxq  %rax, %r11 ;                        \
        adoxq  %rcx, %r12 ;                        \
        movq   0x18+P1, %rdx ;                  \
        mulxq  0x8+P1, %rax, %rcx ;              \
        adcxq  %rax, %r12 ;                        \
        adoxq  %rcx, %r13 ;                        \
        adcxq  %rbx, %r13 ;                        \
        adoxq  %rbx, %r14 ;                        \
        adcq   %rbx, %r14 ;                        \
        xorl   %ebx, %ebx ;                        \
        adcxq  %r9, %r9 ;                          \
        adoxq  %r15, %r9 ;                         \
        movq   0x8+P1, %rdx ;                   \
        mulxq  %rdx, %rax, %rdx ;                   \
        adcxq  %r10, %r10 ;                        \
        adoxq  %rax, %r10 ;                        \
        adcxq  %r11, %r11 ;                        \
        adoxq  %rdx, %r11 ;                        \
        movq   0x10+P1, %rdx ;                  \
        mulxq  %rdx, %rax, %rdx ;                   \
        adcxq  %r12, %r12 ;                        \
        adoxq  %rax, %r12 ;                        \
        adcxq  %r13, %r13 ;                        \
        adoxq  %rdx, %r13 ;                        \
        movq   0x18+P1, %rdx ;                  \
        mulxq  %rdx, %rax, %r15 ;                   \
        adcxq  %r14, %r14 ;                        \
        adoxq  %rax, %r14 ;                        \
        adcxq  %rbx, %r15 ;                        \
        adoxq  %rbx, %r15 ;                        \
        movl   $0x26, %edx ;                       \
        xorl   %ebx, %ebx ;                        \
        mulxq  %r12, %rax, %rcx ;                   \
        adcxq  %rax, %r8 ;                         \
        adoxq  %rcx, %r9 ;                         \
        mulxq  %r13, %rax, %rcx ;                   \
        adcxq  %rax, %r9 ;                         \
        adoxq  %rcx, %r10 ;                        \
        mulxq  %r14, %rax, %rcx ;                   \
        adcxq  %rax, %r10 ;                        \
        adoxq  %rcx, %r11 ;                        \
        mulxq  %r15, %rax, %r12 ;                   \
        adcxq  %rax, %r11 ;                        \
        adoxq  %rbx, %r12 ;                        \
        adcxq  %rbx, %r12 ;                        \
        shldq  $0x1, %r11, %r12 ;                   \
        btr    $0x3f, %r11 ;                       \
        movl   $0x13, %edx ;                       \
        imulq  %r12, %rdx ;                        \
        addq   %rdx, %r8 ;                         \
        adcq   %rbx, %r9 ;                         \
        adcq   %rbx, %r10 ;                        \
        adcq   %rbx, %r11 ;                        \
        movq   %r8, P0 ;                        \
        movq   %r9, 0x8+P0 ;                    \
        movq   %r10, 0x10+P0 ;                  \
        movq   %r11, 0x18+P0

// Plain 4-digit add without any normalization
// With inputs < p_25519 (indeed < 2^255) it still gives a 4-digit result

#define add_4(P0,P1,P2)                         \
        movq    P1, %rax ;                      \
        addq    P2, %rax ;                      \
        movq    %rax, P0 ;                      \
        movq    8+P1, %rax ;                    \
        adcq    8+P2, %rax ;                    \
        movq    %rax, 8+P0 ;                    \
        movq    16+P1, %rax ;                   \
        adcq    16+P2, %rax ;                   \
        movq    %rax, 16+P0 ;                   \
        movq    24+P1, %rax ;                   \
        adcq    24+P2, %rax ;                   \
        movq    %rax, 24+P0

// Add 5-digit inputs and normalize to 4 digits

#define add5_4(P0,P1,P2)                        \
        movq    P1, %r8 ;                       \
        addq    P2, %r8 ;                       \
        movq    8+P1, %r9 ;                     \
        adcq    8+P2, %r9 ;                     \
        movq    16+P1, %r10 ;                   \
        adcq    16+P2, %r10 ;                   \
        movq    24+P1, %r11 ;                   \
        adcq    24+P2, %r11 ;                   \
        movq    32+P1, %r12 ;                   \
        adcq    32+P2, %r12 ;                   \
        xorl    %ebx, %ebx ;                       \
        shldq  $0x1, %r11, %r12 ;                   \
        btr    $0x3f, %r11 ;                       \
        movl   $0x13, %edx ;                       \
        imulq  %r12, %rdx ;                        \
        addq   %rdx, %r8 ;                         \
        adcq   %rbx, %r9 ;                         \
        adcq   %rbx, %r10 ;                        \
        adcq   %rbx, %r11 ;                        \
        movq   %r8, P0 ;                        \
        movq   %r9, 0x8+P0 ;                    \
        movq   %r10, 0x10+P0 ;                  \
        movq   %r11, 0x18+P0

// Subtraction of a pair of numbers < p_25519 just sufficient
// to give a 4-digit result. It actually always does (x - z) + (2^255-19)
// which in turn is done by (x - z) - (2^255+19) discarding the 2^256
// implicitly

#define sub_4(P0,P1,P2)                         \
        movq    P1, %r8 ;                       \
        subq    P2, %r8 ;                       \
        movq    8+P1, %r9 ;                     \
        sbbq    8+P2, %r9 ;                     \
        movq    16+P1, %r10 ;                   \
        sbbq    16+P2, %r10 ;                   \
        movq    24+P1, %rax ;                   \
        sbbq    24+P2, %rax ;                   \
        subq    $19, %r8 ;                         \
        movq    %r8, P0 ;                       \
        sbbq    $0, %r9 ;                          \
        movq    %r9, 8+P0 ;                     \
        sbbq    $0, %r10 ;                         \
        movq    %r10, 16+P0 ;                   \
        sbbq    $0, %rax ;                         \
        btc     $63, %rax ;                        \
        movq    %rax, 24+P0

// Modular subtraction with double modulus 2 * p_25519 = 2^256 - 38

#define sub_twice4(P0,P1,P2)                    \
        movq    P1, %r8 ;                       \
        xorl    %ebx, %ebx ;                       \
        subq    P2, %r8 ;                       \
        movq    8+P1, %r9 ;                     \
        sbbq    8+P2, %r9 ;                     \
        movl    $38, %ecx ;                        \
        movq    16+P1, %r10 ;                   \
        sbbq    16+P2, %r10 ;                   \
        movq    24+P1, %rax ;                   \
        sbbq    24+P2, %rax ;                   \
        cmovncq %rbx, %rcx ;                       \
        subq    %rcx, %r8 ;                        \
        sbbq    %rbx, %r9 ;                        \
        sbbq    %rbx, %r10 ;                       \
        sbbq    %rbx, %rax ;                       \
        movq    %r8, P0 ;                       \
        movq    %r9, 8+P0 ;                     \
        movq    %r10, 16+P0 ;                   \
        movq    %rax, 24+P0

// 5-digit subtraction with upward bias to make it positive, adding
// 1000 * (2^255 - 19) = 2^256 * 500 - 19000, then normalizing to 4 digits

#define sub5_4(P0,P1,P2)                        \
        movq    P1, %r8 ;                       \
        subq    P2, %r8 ;                       \
        movq    8+P1, %r9 ;                     \
        sbbq    8+P2, %r9 ;                     \
        movq    16+P1, %r10 ;                   \
        sbbq    16+P2, %r10 ;                   \
        movq    24+P1, %r11 ;                   \
        sbbq    24+P2, %r11 ;                   \
        movq    32+P1, %r12 ;                   \
        sbbq    32+P2, %r12 ;                   \
        xorl    %ebx, %ebx ;                       \
        subq    $19000, %r8 ;                      \
        sbbq    %rbx, %r9 ;                        \
        sbbq    %rbx, %r10 ;                       \
        sbbq    %rbx, %r11 ;                       \
        sbbq    %rbx, %r12 ;                       \
        addq    $500, %r12 ;                       \
        shldq  $0x1, %r11, %r12 ;                   \
        btr    $0x3f, %r11 ;                       \
        movl   $0x13, %edx ;                       \
        imulq  %r12, %rdx ;                        \
        addq   %rdx, %r8 ;                         \
        adcq   %rbx, %r9 ;                         \
        adcq   %rbx, %r10 ;                        \
        adcq   %rbx, %r11 ;                        \
        movq   %r8, P0 ;                        \
        movq   %r9, 0x8+P0 ;                    \
        movq   %r10, 0x10+P0 ;                  \
        movq   %r11, 0x18+P0

// Combined z = c * x + y with reduction only < 2 * p_25519
// It is assumed that 19 * (c * x + y) < 2^60 * 2^256 so we
// don't need a high mul in the final part.

#define cmadd_4(P0,C1,P2,P3)                    \
        movq    P3, %r8 ;                       \
        movq    8+P3, %r9 ;                     \
        movq    16+P3, %r10 ;                   \
        movq    24+P3, %r11 ;                   \
        xorl    %edi, %edi ;                       \
        movq    $C1, %rdx ;                        \
        mulxq   P2, %rax, %rbx ;                 \
        adcxq   %rax, %r8 ;                        \
        adoxq   %rbx, %r9 ;                        \
        mulxq   8+P2, %rax, %rbx ;               \
        adcxq   %rax, %r9 ;                        \
        adoxq   %rbx, %r10 ;                       \
        mulxq   16+P2, %rax, %rbx ;              \
        adcxq   %rax, %r10 ;                       \
        adoxq   %rbx, %r11 ;                       \
        mulxq   24+P2, %rax, %rbx ;              \
        adcxq   %rax, %r11 ;                       \
        adoxq   %rdi, %rbx ;                       \
        adcxq   %rdi, %rbx ;                       \
        shldq   $0x1, %r11, %rbx ;                  \
        btr     $63, %r11 ;                        \
        movl    $0x13, %edx ;                      \
        imulq   %rdx, %rbx ;                       \
        addq    %rbx, %r8 ;                        \
        adcq    %rdi, %r9 ;                        \
        adcq    %rdi, %r10 ;                       \
        adcq    %rdi, %r11 ;                       \
        movq    %r8, P0 ;                       \
        movq    %r9, 0x8+P0 ;                   \
        movq    %r10, 0x10+P0 ;                 \
        movq    %r11, 0x18+P0

// Multiplex: z := if NZ then x else y

#define mux_4(P0,P1,P2)                         \
        movq    P1, %rax ;                      \
        movq    P2, %rcx ;                      \
        cmovzq  %rcx, %rax ;                       \
        movq    %rax, P0 ;                      \
        movq    8+P1, %rax ;                    \
        movq    8+P2, %rcx ;                    \
        cmovzq  %rcx, %rax ;                       \
        movq    %rax, 8+P0 ;                    \
        movq    16+P1, %rax ;                   \
        movq    16+P2, %rcx ;                   \
        cmovzq  %rcx, %rax ;                       \
        movq    %rax, 16+P0 ;                   \
        movq    24+P1, %rax ;                   \
        movq    24+P2, %rcx ;                   \
        cmovzq  %rcx, %rax ;                       \
        movq    %rax, 24+P0

S2N_BN_SYMBOL(curve25519_pxscalarmul):
        _CET_ENDBR

#if WINDOWS_ABI
        pushq   %rdi
        pushq   %rsi
        movq    %rcx, %rdi
        movq    %rdx, %rsi
        movq    %r8, %rdx
#endif

// Save registers, make room for temps, preserve input arguments.

        pushq   %rbx
        pushq   %rbp
        pushq   %r12
        pushq   %r13
        pushq   %r14
        pushq   %r15
        subq    $NSPACE, %rsp

// Move the input arguments to stable places

        movq    %rdi, res
        movq    %rsi, scalar
        movq    %rdx, point

// Initialize (xn,zn) = (1,0) and (xm,zm) = (x,1) with swap = 0

        movq    $1, %rax
        movq    %rax, 256(%rsp)
        movq    %rax, (%rsp)
        xorl    %eax, %eax
        movq    %rax, swap
        movq    %rax, 96(%rsp)
        movq    %rax, 264(%rsp)
        movq    %rax, 8(%rsp)
        movq    %rax, 104(%rsp)
        movq    %rax, 272(%rsp)
        movq    %rax, 16(%rsp)
        movq    %rax, 112(%rsp)
        movq    %rax, 280(%rsp)
        movq    %rax, 24(%rsp)
        movq    %rax, 120(%rsp)
        movq    (%rdx), %rax
        movq    %rax, 192(%rsp)
        movq    8(%rdx), %rax
        movq    %rax, 200(%rsp)
        movq    16(%rdx), %rax
        movq    %rax, 208(%rsp)
        movq    24(%rdx), %rax
        movq    %rax, 216(%rsp)

// The outer loop from i = 255, ..., i = 0 (inclusive)

        movl    $255, %eax
        movq    %rax, i

curve25519_pxscalarmul_loop:

// sm = xm + zm; sn = xn + zn; dm = xm - zm; dn = xn - zn
// The adds don't need any normalization as they're fed to muls
// Just make sure the subs fit in 4 digits.

        sub_4(dm,xm,zm)
        add_4(sn,xn,zn)
        sub_4(dn,xn,zn)
        add_4(sm,xm,zm)

// ADDING: dmsn = dm * sn; dnsm = sm * dn
// DOUBLING: mux d = xt - zt and s = xt + zt for appropriate choice of (xt,zt)

        mul_5(dmsn,sn,dm)

        movq    scalar, %rax
        movq    i, %rdx
        movq    %rdx, %rcx
        shrq    $6, %rdx
        movq    (%rax,%rdx,8), %rdx
        shrq    %cl, %rdx
        andq    $1, %rdx
        cmpq    swap, %rdx
        movq    %rdx, swap

        mux_4(d,dm,dn)
        mux_4(s,sm,sn)

        mul_5(dnsm,sm,dn)

// DOUBLING: d = (xt - zt)^2 normalized only to 4 digits

        sqr_4(d,d)

// ADDING: dpro = (dmsn - dnsm)^2, spro = (dmsn + dnsm)^2
// DOUBLING: s = (xt + zt)^2, normalized only to 4 digits

        sub5_4(dpro,dmsn,dnsm)
        sqr_4(s,s)
        add5_4(spro,dmsn,dnsm)
        sqr_4(dpro,dpro)

// DOUBLING: p = 4 * xt * zt = s - d

        sub_twice4(p,s,d)

// ADDING: xm' = (dmsn + dnsm)^2

        sqr_p25519(xm,spro)

// DOUBLING: e = 121666 * p + d

        cmadd_4(e,0x1db42,p,d)

// DOUBLING: xn' = (xt + zt)^2 * (xt - zt)^2 = s * d

        mul_p25519(xn,s,d)

// ADDING: zm' = x * (dmsn - dnsm)^2

        movq    point, %rbp
        mul_p25519(zm,dpro,x)

// DOUBLING: zn' = (4 * xt * zt) * ((xt - zt)^2 + 121666 * (4 * xt * zt))
//               = p * (d + 121666 * p)

        mul_p25519(zn,p,e)

// Loop down as far as 0 (inclusive)

        movq    i, %rax
        subq    $1, %rax
        movq    %rax, i
        jnc     curve25519_pxscalarmul_loop

// The main loop does not handle the special input of the 2-torsion
// point = (0,0). In that case we may get a spurious (0,0) as output
// when we want (0,1) [for odd scalar] or (1,0) [for even scalar].
// Test if x = 0 (this is equivalent for curve25519 to y = 0) and if
// so, patch zm = 1 [for odd multiple], xn = 1 [for even multiple].

        movl    $1, %ecx
        movq    point, %rbp
        movq    (%rbp), %rax
        orq     8(%rbp), %rax
        orq     16(%rbp), %rax
        orq     24(%rbp), %rax
        cmovnzq %rcx, %rax
        xorq    $1, %rax
        orq     %rax, (%rsp)
        orq     %rax, 256(%rsp)

// Multiplex into the final outputs

        movq    res, %rbp
        movq    swap, %rax
        testq   %rax, %rax

        mux_4(resx,xm,xn)
        mux_4(resz,zm,zn)

// Restore stack and registers

        addq    $NSPACE, %rsp

        popq    %r15
        popq    %r14
        popq    %r13
        popq    %r12
        popq    %rbp
        popq    %rbx

#if WINDOWS_ABI
        popq   %rsi
        popq   %rdi
#endif
        ret

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack, "", %progbits
#endif
