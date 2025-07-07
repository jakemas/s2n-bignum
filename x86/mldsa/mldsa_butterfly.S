/*
 * Copyright (c) The mldsa-native project authors
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT
 */

.intel_syntax noprefix
.text
.global mldsa_butterfly_instance
mldsa_butterfly_instance:
    # This is the expanded form of butterfly 4,8 with default zeta registers
    # Assumes registers are already set up:
    # ymm0: modulus-related constant (qinv)
    # ymm1, ymm2: zeta values
    # ymm4: l value
    # ymm8: h value
    
    vpmuldq ymm13, ymm1, ymm8
    vmovshdup ymm12, ymm8
    vpmuldq ymm14, ymm1, ymm12
    
    vpmuldq ymm8, ymm2, ymm8
    vpmuldq ymm12, ymm2, ymm12
    
    vpmuldq ymm13, ymm0, ymm13
    vpmuldq ymm14, ymm0, ymm14
    
    vmovshdup ymm8, ymm8
    vpblendd ymm8, ymm8, ymm12, 0xAA
    
    vpsubd ymm12, ymm4, ymm8
    vpaddd ymm4, ymm4, ymm8
    
    vmovshdup ymm13, ymm13
    vpblendd ymm13, ymm13, ymm14, 0xAA
    
    vpaddd ymm8, ymm12, ymm13
    vpsubd ymm4, ymm4, ymm13
    
    ret
