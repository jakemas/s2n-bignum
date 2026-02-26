(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(*                               *)
(* ========================================================================= *)

needs "x86/proofs/base.ml";;
needs "common/mlkem_mldsa.ml";;

(*** print_literal_from_elf "x86/mldsa/mldsa_pointwise_acc_l4.o";;
 ***)

let mldsa_pointwise_acc_l4_mc = define_assert_from_elf "mldsa_pointwise_acc_l4_mc" "x86/mldsa/mldsa_pointwise_acc_l4.o"
[
  0xf3; 0x0f; 0x1e; 0xfa;  (* ENDBR64 *)
  0xc5; 0xfd; 0x6f; 0x41; 0x20;
                           (* VMOVDQA (%_% ymm0) (Memop Word256 (%% (rcx,32))) *)
  0xc5; 0xfd; 0x6f; 0x09;  (* VMOVDQA (%_% ymm1) (Memop Word256 (%% (rcx,0))) *)
  0x31; 0xc0;              (* XOR (% eax) (% eax) *)
  0xc5; 0xfd; 0x6f; 0x36;  (* VMOVDQA (%_% ymm6) (Memop Word256 (%% (rsi,0))) *)
  0xc5; 0x7d; 0x6f; 0x46; 0x20;
                           (* VMOVDQA (%_% ymm8) (Memop Word256 (%% (rsi,32))) *)
  0xc5; 0x7d; 0x6f; 0x12;  (* VMOVDQA (%_% ymm10) (Memop Word256 (%% (rdx,0))) *)
  0xc5; 0x7d; 0x6f; 0x62; 0x20;
                           (* VMOVDQA (%_% ymm12) (Memop Word256 (%% (rdx,32))) *)
  0xc5; 0xc5; 0x73; 0xd6; 0x20;
                           (* VPSRLQ (%_% ymm7) (%_% ymm6) (Imm8 (word 32)) *)
  0xc4; 0xc1; 0x35; 0x73; 0xd0; 0x20;
                           (* VPSRLQ (%_% ymm9) (%_% ymm8) (Imm8 (word 32)) *)
  0xc4; 0x41; 0x7e; 0x16; 0xda;
                           (* VMOVSHDUP (%_% ymm11) (%_% ymm10) *)
  0xc4; 0x41; 0x7e; 0x16; 0xec;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm12) *)
  0xc4; 0xc2; 0x4d; 0x28; 0xf2;
                           (* VPMULDQ (%_% ymm6) (%_% ymm6) (%_% ymm10) *)
  0xc4; 0xc2; 0x45; 0x28; 0xfb;
                           (* VPMULDQ (%_% ymm7) (%_% ymm7) (%_% ymm11) *)
  0xc4; 0x42; 0x3d; 0x28; 0xc4;
                           (* VPMULDQ (%_% ymm8) (%_% ymm8) (%_% ymm12) *)
  0xc4; 0x42; 0x35; 0x28; 0xcd;
                           (* VPMULDQ (%_% ymm9) (%_% ymm9) (%_% ymm13) *)
  0xc5; 0xfd; 0x6f; 0xd6;  (* VMOVDQA (%_% ymm2) (%_% ymm6) *)
  0xc5; 0xfd; 0x6f; 0xdf;  (* VMOVDQA (%_% ymm3) (%_% ymm7) *)
  0xc5; 0x7d; 0x7f; 0xc4;  (* VMOVDQA (%_% ymm4) (%_% ymm8) *)
  0xc5; 0x7d; 0x7f; 0xcd;  (* VMOVDQA (%_% ymm5) (%_% ymm9) *)
  0xc5; 0xfd; 0x6f; 0xb6; 0x00; 0x04; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm6) (Memop Word256 (%% (rsi,1024))) *)
  0xc5; 0x7d; 0x6f; 0x86; 0x20; 0x04; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm8) (Memop Word256 (%% (rsi,1056))) *)
  0xc5; 0x7d; 0x6f; 0x92; 0x00; 0x04; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm10) (Memop Word256 (%% (rdx,1024))) *)
  0xc5; 0x7d; 0x6f; 0xa2; 0x20; 0x04; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm12) (Memop Word256 (%% (rdx,1056))) *)
  0xc5; 0xc5; 0x73; 0xd6; 0x20;
                           (* VPSRLQ (%_% ymm7) (%_% ymm6) (Imm8 (word 32)) *)
  0xc4; 0xc1; 0x35; 0x73; 0xd0; 0x20;
                           (* VPSRLQ (%_% ymm9) (%_% ymm8) (Imm8 (word 32)) *)
  0xc4; 0x41; 0x7e; 0x16; 0xda;
                           (* VMOVSHDUP (%_% ymm11) (%_% ymm10) *)
  0xc4; 0x41; 0x7e; 0x16; 0xec;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm12) *)
  0xc4; 0xc2; 0x4d; 0x28; 0xf2;
                           (* VPMULDQ (%_% ymm6) (%_% ymm6) (%_% ymm10) *)
  0xc4; 0xc2; 0x45; 0x28; 0xfb;
                           (* VPMULDQ (%_% ymm7) (%_% ymm7) (%_% ymm11) *)
  0xc4; 0x42; 0x3d; 0x28; 0xc4;
                           (* VPMULDQ (%_% ymm8) (%_% ymm8) (%_% ymm12) *)
  0xc4; 0x42; 0x35; 0x28; 0xcd;
                           (* VPMULDQ (%_% ymm9) (%_% ymm9) (%_% ymm13) *)
  0xc5; 0xed; 0xd4; 0xd6;  (* VPADDQ (%_% ymm2) (%_% ymm2) (%_% ymm6) *)
  0xc5; 0xe5; 0xd4; 0xdf;  (* VPADDQ (%_% ymm3) (%_% ymm3) (%_% ymm7) *)
  0xc5; 0xbd; 0xd4; 0xe4;  (* VPADDQ (%_% ymm4) (%_% ymm8) (%_% ymm4) *)
  0xc5; 0xb5; 0xd4; 0xed;  (* VPADDQ (%_% ymm5) (%_% ymm9) (%_% ymm5) *)
  0xc5; 0xfd; 0x6f; 0xb6; 0x00; 0x08; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm6) (Memop Word256 (%% (rsi,2048))) *)
  0xc5; 0x7d; 0x6f; 0x86; 0x20; 0x08; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm8) (Memop Word256 (%% (rsi,2080))) *)
  0xc5; 0x7d; 0x6f; 0x92; 0x00; 0x08; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm10) (Memop Word256 (%% (rdx,2048))) *)
  0xc5; 0x7d; 0x6f; 0xa2; 0x20; 0x08; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm12) (Memop Word256 (%% (rdx,2080))) *)
  0xc5; 0xc5; 0x73; 0xd6; 0x20;
                           (* VPSRLQ (%_% ymm7) (%_% ymm6) (Imm8 (word 32)) *)
  0xc4; 0xc1; 0x35; 0x73; 0xd0; 0x20;
                           (* VPSRLQ (%_% ymm9) (%_% ymm8) (Imm8 (word 32)) *)
  0xc4; 0x41; 0x7e; 0x16; 0xda;
                           (* VMOVSHDUP (%_% ymm11) (%_% ymm10) *)
  0xc4; 0x41; 0x7e; 0x16; 0xec;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm12) *)
  0xc4; 0xc2; 0x4d; 0x28; 0xf2;
                           (* VPMULDQ (%_% ymm6) (%_% ymm6) (%_% ymm10) *)
  0xc4; 0xc2; 0x45; 0x28; 0xfb;
                           (* VPMULDQ (%_% ymm7) (%_% ymm7) (%_% ymm11) *)
  0xc4; 0x42; 0x3d; 0x28; 0xc4;
                           (* VPMULDQ (%_% ymm8) (%_% ymm8) (%_% ymm12) *)
  0xc4; 0x42; 0x35; 0x28; 0xcd;
                           (* VPMULDQ (%_% ymm9) (%_% ymm9) (%_% ymm13) *)
  0xc5; 0xed; 0xd4; 0xd6;  (* VPADDQ (%_% ymm2) (%_% ymm2) (%_% ymm6) *)
  0xc5; 0xe5; 0xd4; 0xdf;  (* VPADDQ (%_% ymm3) (%_% ymm3) (%_% ymm7) *)
  0xc5; 0xbd; 0xd4; 0xe4;  (* VPADDQ (%_% ymm4) (%_% ymm8) (%_% ymm4) *)
  0xc5; 0xb5; 0xd4; 0xed;  (* VPADDQ (%_% ymm5) (%_% ymm9) (%_% ymm5) *)
  0xc5; 0xfd; 0x6f; 0xb6; 0x00; 0x0c; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm6) (Memop Word256 (%% (rsi,3072))) *)
  0xc5; 0x7d; 0x6f; 0x86; 0x20; 0x0c; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm8) (Memop Word256 (%% (rsi,3104))) *)
  0xc5; 0x7d; 0x6f; 0x92; 0x00; 0x0c; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm10) (Memop Word256 (%% (rdx,3072))) *)
  0xc5; 0x7d; 0x6f; 0xa2; 0x20; 0x0c; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm12) (Memop Word256 (%% (rdx,3104))) *)
  0xc5; 0xc5; 0x73; 0xd6; 0x20;
                           (* VPSRLQ (%_% ymm7) (%_% ymm6) (Imm8 (word 32)) *)
  0xc4; 0xc1; 0x35; 0x73; 0xd0; 0x20;
                           (* VPSRLQ (%_% ymm9) (%_% ymm8) (Imm8 (word 32)) *)
  0xc4; 0x41; 0x7e; 0x16; 0xda;
                           (* VMOVSHDUP (%_% ymm11) (%_% ymm10) *)
  0xc4; 0x41; 0x7e; 0x16; 0xec;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm12) *)
  0xc4; 0xc2; 0x4d; 0x28; 0xf2;
                           (* VPMULDQ (%_% ymm6) (%_% ymm6) (%_% ymm10) *)
  0xc4; 0xc2; 0x45; 0x28; 0xfb;
                           (* VPMULDQ (%_% ymm7) (%_% ymm7) (%_% ymm11) *)
  0xc4; 0x42; 0x3d; 0x28; 0xc4;
                           (* VPMULDQ (%_% ymm8) (%_% ymm8) (%_% ymm12) *)
  0xc4; 0x42; 0x35; 0x28; 0xcd;
                           (* VPMULDQ (%_% ymm9) (%_% ymm9) (%_% ymm13) *)
  0xc5; 0xed; 0xd4; 0xd6;  (* VPADDQ (%_% ymm2) (%_% ymm2) (%_% ymm6) *)
  0xc5; 0xe5; 0xd4; 0xdf;  (* VPADDQ (%_% ymm3) (%_% ymm3) (%_% ymm7) *)
  0xc5; 0xbd; 0xd4; 0xe4;  (* VPADDQ (%_% ymm4) (%_% ymm8) (%_% ymm4) *)
  0xc5; 0xb5; 0xd4; 0xed;  (* VPADDQ (%_% ymm5) (%_% ymm9) (%_% ymm5) *)
  0xc4; 0xe2; 0x6d; 0x28; 0xf0;
                           (* VPMULDQ (%_% ymm6) (%_% ymm2) (%_% ymm0) *)
  0xc4; 0xe2; 0x65; 0x28; 0xf8;
                           (* VPMULDQ (%_% ymm7) (%_% ymm3) (%_% ymm0) *)
  0xc4; 0x62; 0x5d; 0x28; 0xc0;
                           (* VPMULDQ (%_% ymm8) (%_% ymm4) (%_% ymm0) *)
  0xc4; 0x62; 0x55; 0x28; 0xc8;
                           (* VPMULDQ (%_% ymm9) (%_% ymm5) (%_% ymm0) *)
  0xc4; 0xe2; 0x4d; 0x28; 0xf1;
                           (* VPMULDQ (%_% ymm6) (%_% ymm6) (%_% ymm1) *)
  0xc4; 0xe2; 0x45; 0x28; 0xf9;
                           (* VPMULDQ (%_% ymm7) (%_% ymm7) (%_% ymm1) *)
  0xc4; 0x62; 0x3d; 0x28; 0xc1;
                           (* VPMULDQ (%_% ymm8) (%_% ymm8) (%_% ymm1) *)
  0xc4; 0x62; 0x35; 0x28; 0xc9;
                           (* VPMULDQ (%_% ymm9) (%_% ymm9) (%_% ymm1) *)
  0xc5; 0xed; 0xfb; 0xd6;  (* VPSUBQ (%_% ymm2) (%_% ymm2) (%_% ymm6) *)
  0xc5; 0xe5; 0xfb; 0xdf;  (* VPSUBQ (%_% ymm3) (%_% ymm3) (%_% ymm7) *)
  0xc4; 0xc1; 0x5d; 0xfb; 0xe0;
                           (* VPSUBQ (%_% ymm4) (%_% ymm4) (%_% ymm8) *)
  0xc4; 0xc1; 0x55; 0xfb; 0xe9;
                           (* VPSUBQ (%_% ymm5) (%_% ymm5) (%_% ymm9) *)
  0xc5; 0xed; 0x73; 0xd2; 0x20;
                           (* VPSRLQ (%_% ymm2) (%_% ymm2) (Imm8 (word 32)) *)
  0xc5; 0xfe; 0x16; 0xe4;  (* VMOVSHDUP (%_% ymm4) (%_% ymm4) *)
  0xc4; 0xe3; 0x6d; 0x02; 0xd3; 0xaa;
                           (* VPBLENDD (%_% ymm2) (%_% ymm2) (%_% ymm3) (Imm8 (word 170)) *)
  0xc4; 0xe3; 0x5d; 0x02; 0xe5; 0xaa;
                           (* VPBLENDD (%_% ymm4) (%_% ymm4) (%_% ymm5) (Imm8 (word 170)) *)
  0xc5; 0xfd; 0x7f; 0x17;  (* VMOVDQA (Memop Word256 (%% (rdi,0))) (%_% ymm2) *)
  0xc5; 0xfd; 0x7f; 0x67; 0x20;
                           (* VMOVDQA (Memop Word256 (%% (rdi,32))) (%_% ymm4) *)
  0x48; 0x83; 0xc6; 0x40;  (* ADD (% rsi) (Imm8 (word 64)) *)
  0x48; 0x83; 0xc2; 0x40;  (* ADD (% rdx) (Imm8 (word 64)) *)
  0x48; 0x83; 0xc7; 0x40;  (* ADD (% rdi) (Imm8 (word 64)) *)
  0x83; 0xc0; 0x01;        (* ADD (% eax) (Imm8 (word 1)) *)
  0x83; 0xf8; 0x10;        (* CMP (% eax) (Imm8 (word 16)) *)
  0x0f; 0x82; 0x3a; 0xfe; 0xff; 0xff;
                           (* JB (Imm32 (word 4294966842)) *)
  0xc3                     (* RET *)
];;

let mldsa_pointwise_acc_l4_tmc = define_trimmed "mldsa_pointwise_acc_l4_tmc" mldsa_pointwise_acc_l4_mc;;
let MLDSA_POINTWISE_ACC_L4_TMC_EXEC = X86_MK_CORE_EXEC_RULE mldsa_pointwise_acc_l4_tmc;;

(*** getting PC length/size:
let len_thm = REWRITE_CONV[mldsa_pointwise_acc_l4_tmc] `LENGTH mldsa_pointwise_acc_l4_tmc`;;
let len_computed = LENGTH_CONV (rhs (concl len_thm));;
let final_value = rhs (concl len_computed);;
dest_small_numeral final_value;;

val it : int = 466
pc + 0x1D2, ***)

