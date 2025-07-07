(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Reduction of polynomial coefficients producing nonnegative remainders.    *)
(* ========================================================================= *)

needs "x86/proofs/base.ml";;

(**** print_literal_from_elf "x86/mldsa/mldsa_butterfly.o";;
 ****)

 works:
 (**** print_literal_from_elf "x86/mldsa/avx2_simple6.o";;
 ****)

 # print_literal_from_elf "x86/mldsa/avx2_simple6.o";;
[
  0xb8; 0x2a; 0x00; 0x00; 0x00;
                           (* MOV (% eax) (Imm32 (word 42)) *)
  0xbb; 0x07; 0x00; 0x00; 0x00;
                           (* MOV (% ebx) (Imm32 (word 7)) *)
  0x01; 0xd8;              (* ADD (% eax) (% ebx) *)
  0xc4; 0xe2; 0x7d; 0x58; 0xc0;
                           (* VPBROADCASTD (%_% ymm0) (%_% xmm0) *)
  0xc5; 0xfd; 0xfe; 0xc8;  (* VPADDD (%_% ymm1) (%_% ymm0) (%_% ymm0) *)
  0xc5; 0xf5; 0xfa; 0xd0;  (* VPSUBD (%_% ymm2) (%_% ymm1) (%_% ymm0) *)
  0xc4; 0xe2; 0x75; 0x40; 0xda;
                           (* VPMULLD (%_% ymm3) (%_% ymm1) (%_% ymm2) *)
  0xc5; 0xdd; 0x72; 0xe3; 0x02;
                           (* VPSRAD (%_% ymm4) (%_% ymm3) (Imm8 (word 2)) *)
  0xc4; 0xe2; 0x75; 0x28; 0xea;
                           (* VPMULDQ (%_% ymm5) (%_% ymm1) (%_% ymm2) *)
  0xc5; 0xfe; 0x16; 0xf3;  (* VMOVSHDUP (%_% ymm6) (%_% ymm3) *)
  0xc3                     (* RET *)
];;



 (**** print_literal_from_elf "x86/mldsa/avx2_simple7.o";;
 ****)


(**** print_literal_from_elf "reduce_avx2.o";;
 ****)