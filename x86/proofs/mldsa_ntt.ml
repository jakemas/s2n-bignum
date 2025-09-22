(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* ML-DSA Forward number theoretic transform.                                *)
(* ========================================================================= *)

needs "x86/proofs/base.ml";;
needs "common/mlkem_mldsa.ml";;

(*** print_literal_from_elf "x86/mldsa/mldsa_ntt.o";; ***)

let mldsa_ntt_mc = define_assert_from_elf "mldsa_ntt_mc" "x86/mldsa/mldsa_ntt.o"
[
  0xf3; 0x0f; 0x1e; 0xfa;  (* ENDBR64 *)
  0xc5; 0xfd; 0x6f; 0x06;  (* VMOVDQA (%_% ymm0) (Memop Word256 (%% (rsi,0))) *)
  0xc4; 0xe2; 0x7d; 0x58; 0x8e; 0x84; 0x00; 0x00; 0x00;
                           (* VPBROADCASTD (%_% ymm1) (Memop Word128 (%% (rsi,132))) *)
  0xc4; 0xe2; 0x7d; 0x58; 0x96; 0x24; 0x05; 0x00; 0x00;
                           (* VPBROADCASTD (%_% ymm2) (Memop Word128 (%% (rsi,1316))) *)
  0xc5; 0xfd; 0x6f; 0x27;  (* VMOVDQA (%_% ymm4) (Memop Word256 (%% (rdi,0))) *)
  0xc5; 0xfd; 0x6f; 0xaf; 0x80; 0x00; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm5) (Memop Word256 (%% (rdi,128))) *)
  0xc5; 0xfd; 0x6f; 0xb7; 0x00; 0x01; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm6) (Memop Word256 (%% (rdi,256))) *)
  0xc5; 0xfd; 0x6f; 0xbf; 0x80; 0x01; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm7) (Memop Word256 (%% (rdi,384))) *)
  0xc5; 0x7d; 0x6f; 0x87; 0x00; 0x02; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm8) (Memop Word256 (%% (rdi,512))) *)
  0xc5; 0x7d; 0x6f; 0x8f; 0x80; 0x02; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm9) (Memop Word256 (%% (rdi,640))) *)
  0xc5; 0x7d; 0x6f; 0x97; 0x00; 0x03; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm10) (Memop Word256 (%% (rdi,768))) *)
  0xc5; 0x7d; 0x6f; 0x9f; 0x80; 0x03; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm11) (Memop Word256 (%% (rdi,896))) *)
  0xc4; 0xc2; 0x3d; 0x28; 0xcd;
                           (* VPMULDQ (%_% ymm1) (%_% ymm8) (%_% ymm13) *)
  0xc4; 0x41; 0x7e; 0x16; 0xc4;
                           (* VMOVSHDUP (%_% ymm8) (%_% ymm12) *)
  0xc4; 0xc2; 0x1d; 0x28; 0xce;
                           (* VPMULDQ (%_% ymm1) (%_% ymm12) (%_% ymm14) *)
  0xc4; 0xc2; 0x3d; 0x28; 0xd0;
                           (* VPMULDQ (%_% ymm2) (%_% ymm8) (%_% ymm8) *)
  0xc4; 0xc2; 0x1d; 0x28; 0xd4;
                           (* VPMULDQ (%_% ymm2) (%_% ymm12) (%_% ymm12) *)
  0xc4; 0xc2; 0x15; 0x28; 0xc5;
                           (* VPMULDQ (%_% ymm0) (%_% ymm13) (%_% ymm13) *)
  0xc4; 0xc2; 0x0d; 0x28; 0xc6;
                           (* VPMULDQ (%_% ymm0) (%_% ymm14) (%_% ymm14) *)
  0xc4; 0x41; 0x7e; 0x16; 0xc0;
                           (* VMOVSHDUP (%_% ymm8) (%_% ymm8) *)
  0xc4; 0x43; 0x3d; 0x02; 0xe0; 0xaa;
                           (* VPBLENDD (%_% ymm12) (%_% ymm8) (%_% ymm8) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x5d; 0xfa; 0xc4;
                           (* VPSUBD (%_% ymm8) (%_% ymm4) (%_% ymm12) *)
  0xc5; 0x5d; 0xfe; 0xc4;  (* VPADDD (%_% ymm8) (%_% ymm4) (%_% ymm4) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xf5; 0xaa;
                           (* VPBLENDD (%_% ymm14) (%_% ymm13) (%_% ymm13) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x1d; 0xfe; 0xe8;
                           (* VPADDD (%_% ymm13) (%_% ymm12) (%_% ymm8) *)
  0xc5; 0x5d; 0xfa; 0xec;  (* VPSUBD (%_% ymm13) (%_% ymm4) (%_% ymm4) *)
  0xc4; 0xc2; 0x35; 0x28; 0xcd;
                           (* VPMULDQ (%_% ymm1) (%_% ymm9) (%_% ymm13) *)
  0xc4; 0x41; 0x7e; 0x16; 0xcc;
                           (* VMOVSHDUP (%_% ymm9) (%_% ymm12) *)
  0xc4; 0xc2; 0x1d; 0x28; 0xce;
                           (* VPMULDQ (%_% ymm1) (%_% ymm12) (%_% ymm14) *)
  0xc4; 0xc2; 0x35; 0x28; 0xd1;
                           (* VPMULDQ (%_% ymm2) (%_% ymm9) (%_% ymm9) *)
  0xc4; 0xc2; 0x1d; 0x28; 0xd4;
                           (* VPMULDQ (%_% ymm2) (%_% ymm12) (%_% ymm12) *)
  0xc4; 0xc2; 0x15; 0x28; 0xc5;
                           (* VPMULDQ (%_% ymm0) (%_% ymm13) (%_% ymm13) *)
  0xc4; 0xc2; 0x0d; 0x28; 0xc6;
                           (* VPMULDQ (%_% ymm0) (%_% ymm14) (%_% ymm14) *)
  0xc4; 0x41; 0x7e; 0x16; 0xc9;
                           (* VMOVSHDUP (%_% ymm9) (%_% ymm9) *)
  0xc4; 0x43; 0x35; 0x02; 0xe1; 0xaa;
                           (* VPBLENDD (%_% ymm12) (%_% ymm9) (%_% ymm9) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x55; 0xfa; 0xcc;
                           (* VPSUBD (%_% ymm9) (%_% ymm5) (%_% ymm12) *)
  0xc5; 0x55; 0xfe; 0xcd;  (* VPADDD (%_% ymm9) (%_% ymm5) (%_% ymm5) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xf5; 0xaa;
                           (* VPBLENDD (%_% ymm14) (%_% ymm13) (%_% ymm13) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x1d; 0xfe; 0xe9;
                           (* VPADDD (%_% ymm13) (%_% ymm12) (%_% ymm9) *)
  0xc5; 0x55; 0xfa; 0xed;  (* VPSUBD (%_% ymm13) (%_% ymm5) (%_% ymm5) *)
  0xc4; 0xc2; 0x2d; 0x28; 0xcd;
                           (* VPMULDQ (%_% ymm1) (%_% ymm10) (%_% ymm13) *)
  0xc4; 0x41; 0x7e; 0x16; 0xd4;
                           (* VMOVSHDUP (%_% ymm10) (%_% ymm12) *)
  0xc4; 0xc2; 0x1d; 0x28; 0xce;
                           (* VPMULDQ (%_% ymm1) (%_% ymm12) (%_% ymm14) *)
  0xc4; 0xc2; 0x2d; 0x28; 0xd2;
                           (* VPMULDQ (%_% ymm2) (%_% ymm10) (%_% ymm10) *)
  0xc4; 0xc2; 0x1d; 0x28; 0xd4;
                           (* VPMULDQ (%_% ymm2) (%_% ymm12) (%_% ymm12) *)
  0xc4; 0xc2; 0x15; 0x28; 0xc5;
                           (* VPMULDQ (%_% ymm0) (%_% ymm13) (%_% ymm13) *)
  0xc4; 0xc2; 0x0d; 0x28; 0xc6;
                           (* VPMULDQ (%_% ymm0) (%_% ymm14) (%_% ymm14) *)
  0xc4; 0x41; 0x7e; 0x16; 0xd2;
                           (* VMOVSHDUP (%_% ymm10) (%_% ymm10) *)
  0xc4; 0x43; 0x2d; 0x02; 0xe2; 0xaa;
                           (* VPBLENDD (%_% ymm12) (%_% ymm10) (%_% ymm10) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x4d; 0xfa; 0xd4;
                           (* VPSUBD (%_% ymm10) (%_% ymm6) (%_% ymm12) *)
  0xc5; 0x4d; 0xfe; 0xd6;  (* VPADDD (%_% ymm10) (%_% ymm6) (%_% ymm6) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xf5; 0xaa;
                           (* VPBLENDD (%_% ymm14) (%_% ymm13) (%_% ymm13) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x1d; 0xfe; 0xea;
                           (* VPADDD (%_% ymm13) (%_% ymm12) (%_% ymm10) *)
  0xc5; 0x4d; 0xfa; 0xee;  (* VPSUBD (%_% ymm13) (%_% ymm6) (%_% ymm6) *)
  0xc4; 0xc2; 0x25; 0x28; 0xcd;
                           (* VPMULDQ (%_% ymm1) (%_% ymm11) (%_% ymm13) *)
  0xc4; 0x41; 0x7e; 0x16; 0xdc;
                           (* VMOVSHDUP (%_% ymm11) (%_% ymm12) *)
  0xc4; 0xc2; 0x1d; 0x28; 0xce;
                           (* VPMULDQ (%_% ymm1) (%_% ymm12) (%_% ymm14) *)
  0xc4; 0xc2; 0x25; 0x28; 0xd3;
                           (* VPMULDQ (%_% ymm2) (%_% ymm11) (%_% ymm11) *)
  0xc4; 0xc2; 0x1d; 0x28; 0xd4;
                           (* VPMULDQ (%_% ymm2) (%_% ymm12) (%_% ymm12) *)
  0xc4; 0xc2; 0x15; 0x28; 0xc5;
                           (* VPMULDQ (%_% ymm0) (%_% ymm13) (%_% ymm13) *)
  0xc4; 0xc2; 0x0d; 0x28; 0xc6;
                           (* VPMULDQ (%_% ymm0) (%_% ymm14) (%_% ymm14) *)
  0xc4; 0x41; 0x7e; 0x16; 0xdb;
                           (* VMOVSHDUP (%_% ymm11) (%_% ymm11) *)
  0xc4; 0x43; 0x25; 0x02; 0xe3; 0xaa;
                           (* VPBLENDD (%_% ymm12) (%_% ymm11) (%_% ymm11) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x45; 0xfa; 0xdc;
                           (* VPSUBD (%_% ymm11) (%_% ymm7) (%_% ymm12) *)
  0xc5; 0x45; 0xfe; 0xdf;  (* VPADDD (%_% ymm11) (%_% ymm7) (%_% ymm7) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xf5; 0xaa;
                           (* VPBLENDD (%_% ymm14) (%_% ymm13) (%_% ymm13) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x1d; 0xfe; 0xeb;
                           (* VPADDD (%_% ymm13) (%_% ymm12) (%_% ymm11) *)
  0xc5; 0x45; 0xfa; 0xef;  (* VPSUBD (%_% ymm13) (%_% ymm7) (%_% ymm7) *)
  0xc4; 0xe2; 0x7d; 0x58; 0x8e; 0x88; 0x00; 0x00; 0x00;
                           (* VPBROADCASTD (%_% ymm1) (Memop Word128 (%% (rsi,136))) *)
  0xc4; 0xe2; 0x7d; 0x58; 0x96; 0x28; 0x05; 0x00; 0x00;
                           (* VPBROADCASTD (%_% ymm2) (Memop Word128 (%% (rsi,1320))) *)
  0xc4; 0xc2; 0x4d; 0x28; 0xcd;
                           (* VPMULDQ (%_% ymm1) (%_% ymm6) (%_% ymm13) *)
  0xc4; 0xc1; 0x7e; 0x16; 0xf4;
                           (* VMOVSHDUP (%_% ymm6) (%_% ymm12) *)
  0xc4; 0xc2; 0x1d; 0x28; 0xce;
                           (* VPMULDQ (%_% ymm1) (%_% ymm12) (%_% ymm14) *)
  0xc4; 0xe2; 0x4d; 0x28; 0xd6;
                           (* VPMULDQ (%_% ymm2) (%_% ymm6) (%_% ymm6) *)
  0xc4; 0xc2; 0x1d; 0x28; 0xd4;
                           (* VPMULDQ (%_% ymm2) (%_% ymm12) (%_% ymm12) *)
  0xc4; 0xc2; 0x15; 0x28; 0xc5;
                           (* VPMULDQ (%_% ymm0) (%_% ymm13) (%_% ymm13) *)
  0xc4; 0xc2; 0x0d; 0x28; 0xc6;
                           (* VPMULDQ (%_% ymm0) (%_% ymm14) (%_% ymm14) *)
  0xc5; 0xfe; 0x16; 0xf6;  (* VMOVSHDUP (%_% ymm6) (%_% ymm6) *)
  0xc4; 0x63; 0x4d; 0x02; 0xe6; 0xaa;
                           (* VPBLENDD (%_% ymm12) (%_% ymm6) (%_% ymm6) (Imm8 (word 170)) *)
  0xc4; 0xc1; 0x5d; 0xfa; 0xf4;
                           (* VPSUBD (%_% ymm6) (%_% ymm4) (%_% ymm12) *)
  0xc5; 0xdd; 0xfe; 0xf4;  (* VPADDD (%_% ymm6) (%_% ymm4) (%_% ymm4) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xf5; 0xaa;
                           (* VPBLENDD (%_% ymm14) (%_% ymm13) (%_% ymm13) (Imm8 (word 170)) *)
  0xc5; 0x1d; 0xfe; 0xee;  (* VPADDD (%_% ymm13) (%_% ymm12) (%_% ymm6) *)
  0xc5; 0x5d; 0xfa; 0xec;  (* VPSUBD (%_% ymm13) (%_% ymm4) (%_% ymm4) *)
  0xc4; 0xc2; 0x45; 0x28; 0xcd;
                           (* VPMULDQ (%_% ymm1) (%_% ymm7) (%_% ymm13) *)
  0xc4; 0xc1; 0x7e; 0x16; 0xfc;
                           (* VMOVSHDUP (%_% ymm7) (%_% ymm12) *)
  0xc4; 0xc2; 0x1d; 0x28; 0xce;
                           (* VPMULDQ (%_% ymm1) (%_% ymm12) (%_% ymm14) *)
  0xc4; 0xe2; 0x45; 0x28; 0xd7;
                           (* VPMULDQ (%_% ymm2) (%_% ymm7) (%_% ymm7) *)
  0xc4; 0xc2; 0x1d; 0x28; 0xd4;
                           (* VPMULDQ (%_% ymm2) (%_% ymm12) (%_% ymm12) *)
  0xc4; 0xc2; 0x15; 0x28; 0xc5;
                           (* VPMULDQ (%_% ymm0) (%_% ymm13) (%_% ymm13) *)
  0xc4; 0xc2; 0x0d; 0x28; 0xc6;
                           (* VPMULDQ (%_% ymm0) (%_% ymm14) (%_% ymm14) *)
  0xc5; 0xfe; 0x16; 0xff;  (* VMOVSHDUP (%_% ymm7) (%_% ymm7) *)
  0xc4; 0x63; 0x45; 0x02; 0xe7; 0xaa;
                           (* VPBLENDD (%_% ymm12) (%_% ymm7) (%_% ymm7) (Imm8 (word 170)) *)
  0xc4; 0xc1; 0x55; 0xfa; 0xfc;
                           (* VPSUBD (%_% ymm7) (%_% ymm5) (%_% ymm12) *)
  0xc5; 0xd5; 0xfe; 0xfd;  (* VPADDD (%_% ymm7) (%_% ymm5) (%_% ymm5) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xf5; 0xaa;
                           (* VPBLENDD (%_% ymm14) (%_% ymm13) (%_% ymm13) (Imm8 (word 170)) *)
  0xc5; 0x1d; 0xfe; 0xef;  (* VPADDD (%_% ymm13) (%_% ymm12) (%_% ymm7) *)
  0xc5; 0x55; 0xfa; 0xed;  (* VPSUBD (%_% ymm13) (%_% ymm5) (%_% ymm5) *)
  0xc4; 0xe2; 0x7d; 0x58; 0x8e; 0x8c; 0x00; 0x00; 0x00;
                           (* VPBROADCASTD (%_% ymm1) (Memop Word128 (%% (rsi,140))) *)
  0xc4; 0xe2; 0x7d; 0x58; 0x96; 0x2c; 0x05; 0x00; 0x00;
                           (* VPBROADCASTD (%_% ymm2) (Memop Word128 (%% (rsi,1324))) *)
  0xc4; 0xc2; 0x2d; 0x28; 0xcd;
                           (* VPMULDQ (%_% ymm1) (%_% ymm10) (%_% ymm13) *)
  0xc4; 0x41; 0x7e; 0x16; 0xd4;
                           (* VMOVSHDUP (%_% ymm10) (%_% ymm12) *)
  0xc4; 0xc2; 0x1d; 0x28; 0xce;
                           (* VPMULDQ (%_% ymm1) (%_% ymm12) (%_% ymm14) *)
  0xc4; 0xc2; 0x2d; 0x28; 0xd2;
                           (* VPMULDQ (%_% ymm2) (%_% ymm10) (%_% ymm10) *)
  0xc4; 0xc2; 0x1d; 0x28; 0xd4;
                           (* VPMULDQ (%_% ymm2) (%_% ymm12) (%_% ymm12) *)
  0xc4; 0xc2; 0x15; 0x28; 0xc5;
                           (* VPMULDQ (%_% ymm0) (%_% ymm13) (%_% ymm13) *)
  0xc4; 0xc2; 0x0d; 0x28; 0xc6;
                           (* VPMULDQ (%_% ymm0) (%_% ymm14) (%_% ymm14) *)
  0xc4; 0x41; 0x7e; 0x16; 0xd2;
                           (* VMOVSHDUP (%_% ymm10) (%_% ymm10) *)
  0xc4; 0x43; 0x2d; 0x02; 0xe2; 0xaa;
                           (* VPBLENDD (%_% ymm12) (%_% ymm10) (%_% ymm10) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x3d; 0xfa; 0xd4;
                           (* VPSUBD (%_% ymm10) (%_% ymm8) (%_% ymm12) *)
  0xc4; 0x41; 0x3d; 0xfe; 0xd0;
                           (* VPADDD (%_% ymm10) (%_% ymm8) (%_% ymm8) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xf5; 0xaa;
                           (* VPBLENDD (%_% ymm14) (%_% ymm13) (%_% ymm13) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x1d; 0xfe; 0xea;
                           (* VPADDD (%_% ymm13) (%_% ymm12) (%_% ymm10) *)
  0xc4; 0x41; 0x3d; 0xfa; 0xe8;
                           (* VPSUBD (%_% ymm13) (%_% ymm8) (%_% ymm8) *)
  0xc4; 0xc2; 0x25; 0x28; 0xcd;
                           (* VPMULDQ (%_% ymm1) (%_% ymm11) (%_% ymm13) *)
  0xc4; 0x41; 0x7e; 0x16; 0xdc;
                           (* VMOVSHDUP (%_% ymm11) (%_% ymm12) *)
  0xc4; 0xc2; 0x1d; 0x28; 0xce;
                           (* VPMULDQ (%_% ymm1) (%_% ymm12) (%_% ymm14) *)
  0xc4; 0xc2; 0x25; 0x28; 0xd3;
                           (* VPMULDQ (%_% ymm2) (%_% ymm11) (%_% ymm11) *)
  0xc4; 0xc2; 0x1d; 0x28; 0xd4;
                           (* VPMULDQ (%_% ymm2) (%_% ymm12) (%_% ymm12) *)
  0xc4; 0xc2; 0x15; 0x28; 0xc5;
                           (* VPMULDQ (%_% ymm0) (%_% ymm13) (%_% ymm13) *)
  0xc4; 0xc2; 0x0d; 0x28; 0xc6;
                           (* VPMULDQ (%_% ymm0) (%_% ymm14) (%_% ymm14) *)
  0xc4; 0x41; 0x7e; 0x16; 0xdb;
                           (* VMOVSHDUP (%_% ymm11) (%_% ymm11) *)
  0xc4; 0x43; 0x25; 0x02; 0xe3; 0xaa;
                           (* VPBLENDD (%_% ymm12) (%_% ymm11) (%_% ymm11) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x35; 0xfa; 0xdc;
                           (* VPSUBD (%_% ymm11) (%_% ymm9) (%_% ymm12) *)
  0xc4; 0x41; 0x35; 0xfe; 0xd9;
                           (* VPADDD (%_% ymm11) (%_% ymm9) (%_% ymm9) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xf5; 0xaa;
                           (* VPBLENDD (%_% ymm14) (%_% ymm13) (%_% ymm13) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x1d; 0xfe; 0xeb;
                           (* VPADDD (%_% ymm13) (%_% ymm12) (%_% ymm11) *)
  0xc4; 0x41; 0x35; 0xfa; 0xe9;
                           (* VPSUBD (%_% ymm13) (%_% ymm9) (%_% ymm9) *)
  0xc5; 0xfd; 0x7f; 0x27;  (* VMOVDQA (Memop Word256 (%% (rdi,0))) (%_% ymm4) *)
  0xc5; 0xfd; 0x7f; 0xaf; 0x80; 0x00; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,128))) (%_% ymm5) *)
  0xc5; 0xfd; 0x7f; 0xb7; 0x00; 0x01; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,256))) (%_% ymm6) *)
  0xc5; 0xfd; 0x7f; 0xbf; 0x80; 0x01; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,384))) (%_% ymm7) *)
  0xc5; 0x7d; 0x7f; 0x87; 0x00; 0x02; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,512))) (%_% ymm8) *)
  0xc5; 0x7d; 0x7f; 0x8f; 0x80; 0x02; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,640))) (%_% ymm9) *)
  0xc5; 0x7d; 0x7f; 0x97; 0x00; 0x03; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,768))) (%_% ymm10) *)
  0xc5; 0x7d; 0x7f; 0x9f; 0x80; 0x03; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,896))) (%_% ymm11) *)
  0xc4; 0xe2; 0x7d; 0x58; 0x8e; 0x84; 0x00; 0x00; 0x00;
                           (* VPBROADCASTD (%_% ymm1) (Memop Word128 (%% (rsi,132))) *)
  0xc4; 0xe2; 0x7d; 0x58; 0x96; 0x24; 0x05; 0x00; 0x00;
                           (* VPBROADCASTD (%_% ymm2) (Memop Word128 (%% (rsi,1316))) *)
  0xc5; 0xfd; 0x6f; 0x67; 0x20;
                           (* VMOVDQA (%_% ymm4) (Memop Word256 (%% (rdi,32))) *)
  0xc5; 0xfd; 0x6f; 0xaf; 0xa0; 0x00; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm5) (Memop Word256 (%% (rdi,160))) *)
  0xc5; 0xfd; 0x6f; 0xb7; 0x20; 0x01; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm6) (Memop Word256 (%% (rdi,288))) *)
  0xc5; 0xfd; 0x6f; 0xbf; 0xa0; 0x01; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm7) (Memop Word256 (%% (rdi,416))) *)
  0xc5; 0x7d; 0x6f; 0x87; 0x20; 0x02; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm8) (Memop Word256 (%% (rdi,544))) *)
  0xc5; 0x7d; 0x6f; 0x8f; 0xa0; 0x02; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm9) (Memop Word256 (%% (rdi,672))) *)
  0xc5; 0x7d; 0x6f; 0x97; 0x20; 0x03; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm10) (Memop Word256 (%% (rdi,800))) *)
  0xc5; 0x7d; 0x6f; 0x9f; 0xa0; 0x03; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm11) (Memop Word256 (%% (rdi,928))) *)
  0xc4; 0xc2; 0x3d; 0x28; 0xcd;
                           (* VPMULDQ (%_% ymm1) (%_% ymm8) (%_% ymm13) *)
  0xc4; 0x41; 0x7e; 0x16; 0xc4;
                           (* VMOVSHDUP (%_% ymm8) (%_% ymm12) *)
  0xc4; 0xc2; 0x1d; 0x28; 0xce;
                           (* VPMULDQ (%_% ymm1) (%_% ymm12) (%_% ymm14) *)
  0xc4; 0xc2; 0x3d; 0x28; 0xd0;
                           (* VPMULDQ (%_% ymm2) (%_% ymm8) (%_% ymm8) *)
  0xc4; 0xc2; 0x1d; 0x28; 0xd4;
                           (* VPMULDQ (%_% ymm2) (%_% ymm12) (%_% ymm12) *)
  0xc4; 0xc2; 0x15; 0x28; 0xc5;
                           (* VPMULDQ (%_% ymm0) (%_% ymm13) (%_% ymm13) *)
  0xc4; 0xc2; 0x0d; 0x28; 0xc6;
                           (* VPMULDQ (%_% ymm0) (%_% ymm14) (%_% ymm14) *)
  0xc4; 0x41; 0x7e; 0x16; 0xc0;
                           (* VMOVSHDUP (%_% ymm8) (%_% ymm8) *)
  0xc4; 0x43; 0x3d; 0x02; 0xe0; 0xaa;
                           (* VPBLENDD (%_% ymm12) (%_% ymm8) (%_% ymm8) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x5d; 0xfa; 0xc4;
                           (* VPSUBD (%_% ymm8) (%_% ymm4) (%_% ymm12) *)
  0xc5; 0x5d; 0xfe; 0xc4;  (* VPADDD (%_% ymm8) (%_% ymm4) (%_% ymm4) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xf5; 0xaa;
                           (* VPBLENDD (%_% ymm14) (%_% ymm13) (%_% ymm13) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x1d; 0xfe; 0xe8;
                           (* VPADDD (%_% ymm13) (%_% ymm12) (%_% ymm8) *)
  0xc5; 0x5d; 0xfa; 0xec;  (* VPSUBD (%_% ymm13) (%_% ymm4) (%_% ymm4) *)
  0xc4; 0xc2; 0x35; 0x28; 0xcd;
                           (* VPMULDQ (%_% ymm1) (%_% ymm9) (%_% ymm13) *)
  0xc4; 0x41; 0x7e; 0x16; 0xcc;
                           (* VMOVSHDUP (%_% ymm9) (%_% ymm12) *)
  0xc4; 0xc2; 0x1d; 0x28; 0xce;
                           (* VPMULDQ (%_% ymm1) (%_% ymm12) (%_% ymm14) *)
  0xc4; 0xc2; 0x35; 0x28; 0xd1;
                           (* VPMULDQ (%_% ymm2) (%_% ymm9) (%_% ymm9) *)
  0xc4; 0xc2; 0x1d; 0x28; 0xd4;
                           (* VPMULDQ (%_% ymm2) (%_% ymm12) (%_% ymm12) *)
  0xc4; 0xc2; 0x15; 0x28; 0xc5;
                           (* VPMULDQ (%_% ymm0) (%_% ymm13) (%_% ymm13) *)
  0xc4; 0xc2; 0x0d; 0x28; 0xc6;
                           (* VPMULDQ (%_% ymm0) (%_% ymm14) (%_% ymm14) *)
  0xc4; 0x41; 0x7e; 0x16; 0xc9;
                           (* VMOVSHDUP (%_% ymm9) (%_% ymm9) *)
  0xc4; 0x43; 0x35; 0x02; 0xe1; 0xaa;
                           (* VPBLENDD (%_% ymm12) (%_% ymm9) (%_% ymm9) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x55; 0xfa; 0xcc;
                           (* VPSUBD (%_% ymm9) (%_% ymm5) (%_% ymm12) *)
  0xc5; 0x55; 0xfe; 0xcd;  (* VPADDD (%_% ymm9) (%_% ymm5) (%_% ymm5) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xf5; 0xaa;
                           (* VPBLENDD (%_% ymm14) (%_% ymm13) (%_% ymm13) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x1d; 0xfe; 0xe9;
                           (* VPADDD (%_% ymm13) (%_% ymm12) (%_% ymm9) *)
  0xc5; 0x55; 0xfa; 0xed;  (* VPSUBD (%_% ymm13) (%_% ymm5) (%_% ymm5) *)
  0xc4; 0xc2; 0x2d; 0x28; 0xcd;
                           (* VPMULDQ (%_% ymm1) (%_% ymm10) (%_% ymm13) *)
  0xc4; 0x41; 0x7e; 0x16; 0xd4;
                           (* VMOVSHDUP (%_% ymm10) (%_% ymm12) *)
  0xc4; 0xc2; 0x1d; 0x28; 0xce;
                           (* VPMULDQ (%_% ymm1) (%_% ymm12) (%_% ymm14) *)
  0xc4; 0xc2; 0x2d; 0x28; 0xd2;
                           (* VPMULDQ (%_% ymm2) (%_% ymm10) (%_% ymm10) *)
  0xc4; 0xc2; 0x1d; 0x28; 0xd4;
                           (* VPMULDQ (%_% ymm2) (%_% ymm12) (%_% ymm12) *)
  0xc4; 0xc2; 0x15; 0x28; 0xc5;
                           (* VPMULDQ (%_% ymm0) (%_% ymm13) (%_% ymm13) *)
  0xc4; 0xc2; 0x0d; 0x28; 0xc6;
                           (* VPMULDQ (%_% ymm0) (%_% ymm14) (%_% ymm14) *)
  0xc4; 0x41; 0x7e; 0x16; 0xd2;
                           (* VMOVSHDUP (%_% ymm10) (%_% ymm10) *)
  0xc4; 0x43; 0x2d; 0x02; 0xe2; 0xaa;
                           (* VPBLENDD (%_% ymm12) (%_% ymm10) (%_% ymm10) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x4d; 0xfa; 0xd4;
                           (* VPSUBD (%_% ymm10) (%_% ymm6) (%_% ymm12) *)
  0xc5; 0x4d; 0xfe; 0xd6;  (* VPADDD (%_% ymm10) (%_% ymm6) (%_% ymm6) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xf5; 0xaa;
                           (* VPBLENDD (%_% ymm14) (%_% ymm13) (%_% ymm13) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x1d; 0xfe; 0xea;
                           (* VPADDD (%_% ymm13) (%_% ymm12) (%_% ymm10) *)
  0xc5; 0x4d; 0xfa; 0xee;  (* VPSUBD (%_% ymm13) (%_% ymm6) (%_% ymm6) *)
  0xc4; 0xc2; 0x25; 0x28; 0xcd;
                           (* VPMULDQ (%_% ymm1) (%_% ymm11) (%_% ymm13) *)
  0xc4; 0x41; 0x7e; 0x16; 0xdc;
                           (* VMOVSHDUP (%_% ymm11) (%_% ymm12) *)
  0xc4; 0xc2; 0x1d; 0x28; 0xce;
                           (* VPMULDQ (%_% ymm1) (%_% ymm12) (%_% ymm14) *)
  0xc4; 0xc2; 0x25; 0x28; 0xd3;
                           (* VPMULDQ (%_% ymm2) (%_% ymm11) (%_% ymm11) *)
  0xc4; 0xc2; 0x1d; 0x28; 0xd4;
                           (* VPMULDQ (%_% ymm2) (%_% ymm12) (%_% ymm12) *)
  0xc4; 0xc2; 0x15; 0x28; 0xc5;
                           (* VPMULDQ (%_% ymm0) (%_% ymm13) (%_% ymm13) *)
  0xc4; 0xc2; 0x0d; 0x28; 0xc6;
                           (* VPMULDQ (%_% ymm0) (%_% ymm14) (%_% ymm14) *)
  0xc4; 0x41; 0x7e; 0x16; 0xdb;
                           (* VMOVSHDUP (%_% ymm11) (%_% ymm11) *)
  0xc4; 0x43; 0x25; 0x02; 0xe3; 0xaa;
                           (* VPBLENDD (%_% ymm12) (%_% ymm11) (%_% ymm11) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x45; 0xfa; 0xdc;
                           (* VPSUBD (%_% ymm11) (%_% ymm7) (%_% ymm12) *)
  0xc5; 0x45; 0xfe; 0xdf;  (* VPADDD (%_% ymm11) (%_% ymm7) (%_% ymm7) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xf5; 0xaa;
                           (* VPBLENDD (%_% ymm14) (%_% ymm13) (%_% ymm13) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x1d; 0xfe; 0xeb;
                           (* VPADDD (%_% ymm13) (%_% ymm12) (%_% ymm11) *)
  0xc5; 0x45; 0xfa; 0xef;  (* VPSUBD (%_% ymm13) (%_% ymm7) (%_% ymm7) *)
  0xc4; 0xe2; 0x7d; 0x58; 0x8e; 0x88; 0x00; 0x00; 0x00;
                           (* VPBROADCASTD (%_% ymm1) (Memop Word128 (%% (rsi,136))) *)
  0xc4; 0xe2; 0x7d; 0x58; 0x96; 0x28; 0x05; 0x00; 0x00;
                           (* VPBROADCASTD (%_% ymm2) (Memop Word128 (%% (rsi,1320))) *)
  0xc4; 0xc2; 0x4d; 0x28; 0xcd;
                           (* VPMULDQ (%_% ymm1) (%_% ymm6) (%_% ymm13) *)
  0xc4; 0xc1; 0x7e; 0x16; 0xf4;
                           (* VMOVSHDUP (%_% ymm6) (%_% ymm12) *)
  0xc4; 0xc2; 0x1d; 0x28; 0xce;
                           (* VPMULDQ (%_% ymm1) (%_% ymm12) (%_% ymm14) *)
  0xc4; 0xe2; 0x4d; 0x28; 0xd6;
                           (* VPMULDQ (%_% ymm2) (%_% ymm6) (%_% ymm6) *)
  0xc4; 0xc2; 0x1d; 0x28; 0xd4;
                           (* VPMULDQ (%_% ymm2) (%_% ymm12) (%_% ymm12) *)
  0xc4; 0xc2; 0x15; 0x28; 0xc5;
                           (* VPMULDQ (%_% ymm0) (%_% ymm13) (%_% ymm13) *)
  0xc4; 0xc2; 0x0d; 0x28; 0xc6;
                           (* VPMULDQ (%_% ymm0) (%_% ymm14) (%_% ymm14) *)
  0xc5; 0xfe; 0x16; 0xf6;  (* VMOVSHDUP (%_% ymm6) (%_% ymm6) *)
  0xc4; 0x63; 0x4d; 0x02; 0xe6; 0xaa;
                           (* VPBLENDD (%_% ymm12) (%_% ymm6) (%_% ymm6) (Imm8 (word 170)) *)
  0xc4; 0xc1; 0x5d; 0xfa; 0xf4;
                           (* VPSUBD (%_% ymm6) (%_% ymm4) (%_% ymm12) *)
  0xc5; 0xdd; 0xfe; 0xf4;  (* VPADDD (%_% ymm6) (%_% ymm4) (%_% ymm4) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xf5; 0xaa;
                           (* VPBLENDD (%_% ymm14) (%_% ymm13) (%_% ymm13) (Imm8 (word 170)) *)
  0xc5; 0x1d; 0xfe; 0xee;  (* VPADDD (%_% ymm13) (%_% ymm12) (%_% ymm6) *)
  0xc5; 0x5d; 0xfa; 0xec;  (* VPSUBD (%_% ymm13) (%_% ymm4) (%_% ymm4) *)
  0xc4; 0xc2; 0x45; 0x28; 0xcd;
                           (* VPMULDQ (%_% ymm1) (%_% ymm7) (%_% ymm13) *)
  0xc4; 0xc1; 0x7e; 0x16; 0xfc;
                           (* VMOVSHDUP (%_% ymm7) (%_% ymm12) *)
  0xc4; 0xc2; 0x1d; 0x28; 0xce;
                           (* VPMULDQ (%_% ymm1) (%_% ymm12) (%_% ymm14) *)
  0xc4; 0xe2; 0x45; 0x28; 0xd7;
                           (* VPMULDQ (%_% ymm2) (%_% ymm7) (%_% ymm7) *)
  0xc4; 0xc2; 0x1d; 0x28; 0xd4;
                           (* VPMULDQ (%_% ymm2) (%_% ymm12) (%_% ymm12) *)
  0xc4; 0xc2; 0x15; 0x28; 0xc5;
                           (* VPMULDQ (%_% ymm0) (%_% ymm13) (%_% ymm13) *)
  0xc4; 0xc2; 0x0d; 0x28; 0xc6;
                           (* VPMULDQ (%_% ymm0) (%_% ymm14) (%_% ymm14) *)
  0xc5; 0xfe; 0x16; 0xff;  (* VMOVSHDUP (%_% ymm7) (%_% ymm7) *)
  0xc4; 0x63; 0x45; 0x02; 0xe7; 0xaa;
                           (* VPBLENDD (%_% ymm12) (%_% ymm7) (%_% ymm7) (Imm8 (word 170)) *)
  0xc4; 0xc1; 0x55; 0xfa; 0xfc;
                           (* VPSUBD (%_% ymm7) (%_% ymm5) (%_% ymm12) *)
  0xc5; 0xd5; 0xfe; 0xfd;  (* VPADDD (%_% ymm7) (%_% ymm5) (%_% ymm5) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xf5; 0xaa;
                           (* VPBLENDD (%_% ymm14) (%_% ymm13) (%_% ymm13) (Imm8 (word 170)) *)
  0xc5; 0x1d; 0xfe; 0xef;  (* VPADDD (%_% ymm13) (%_% ymm12) (%_% ymm7) *)
  0xc5; 0x55; 0xfa; 0xed;  (* VPSUBD (%_% ymm13) (%_% ymm5) (%_% ymm5) *)
  0xc4; 0xe2; 0x7d; 0x58; 0x8e; 0x8c; 0x00; 0x00; 0x00;
                           (* VPBROADCASTD (%_% ymm1) (Memop Word128 (%% (rsi,140))) *)
  0xc4; 0xe2; 0x7d; 0x58; 0x96; 0x2c; 0x05; 0x00; 0x00;
                           (* VPBROADCASTD (%_% ymm2) (Memop Word128 (%% (rsi,1324))) *)
  0xc4; 0xc2; 0x2d; 0x28; 0xcd;
                           (* VPMULDQ (%_% ymm1) (%_% ymm10) (%_% ymm13) *)
  0xc4; 0x41; 0x7e; 0x16; 0xd4;
                           (* VMOVSHDUP (%_% ymm10) (%_% ymm12) *)
  0xc4; 0xc2; 0x1d; 0x28; 0xce;
                           (* VPMULDQ (%_% ymm1) (%_% ymm12) (%_% ymm14) *)
  0xc4; 0xc2; 0x2d; 0x28; 0xd2;
                           (* VPMULDQ (%_% ymm2) (%_% ymm10) (%_% ymm10) *)
  0xc4; 0xc2; 0x1d; 0x28; 0xd4;
                           (* VPMULDQ (%_% ymm2) (%_% ymm12) (%_% ymm12) *)
  0xc4; 0xc2; 0x15; 0x28; 0xc5;
                           (* VPMULDQ (%_% ymm0) (%_% ymm13) (%_% ymm13) *)
  0xc4; 0xc2; 0x0d; 0x28; 0xc6;
                           (* VPMULDQ (%_% ymm0) (%_% ymm14) (%_% ymm14) *)
  0xc4; 0x41; 0x7e; 0x16; 0xd2;
                           (* VMOVSHDUP (%_% ymm10) (%_% ymm10) *)
  0xc4; 0x43; 0x2d; 0x02; 0xe2; 0xaa;
                           (* VPBLENDD (%_% ymm12) (%_% ymm10) (%_% ymm10) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x3d; 0xfa; 0xd4;
                           (* VPSUBD (%_% ymm10) (%_% ymm8) (%_% ymm12) *)
  0xc4; 0x41; 0x3d; 0xfe; 0xd0;
                           (* VPADDD (%_% ymm10) (%_% ymm8) (%_% ymm8) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xf5; 0xaa;
                           (* VPBLENDD (%_% ymm14) (%_% ymm13) (%_% ymm13) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x1d; 0xfe; 0xea;
                           (* VPADDD (%_% ymm13) (%_% ymm12) (%_% ymm10) *)
  0xc4; 0x41; 0x3d; 0xfa; 0xe8;
                           (* VPSUBD (%_% ymm13) (%_% ymm8) (%_% ymm8) *)
  0xc4; 0xc2; 0x25; 0x28; 0xcd;
                           (* VPMULDQ (%_% ymm1) (%_% ymm11) (%_% ymm13) *)
  0xc4; 0x41; 0x7e; 0x16; 0xdc;
                           (* VMOVSHDUP (%_% ymm11) (%_% ymm12) *)
  0xc4; 0xc2; 0x1d; 0x28; 0xce;
                           (* VPMULDQ (%_% ymm1) (%_% ymm12) (%_% ymm14) *)
  0xc4; 0xc2; 0x25; 0x28; 0xd3;
                           (* VPMULDQ (%_% ymm2) (%_% ymm11) (%_% ymm11) *)
  0xc4; 0xc2; 0x1d; 0x28; 0xd4;
                           (* VPMULDQ (%_% ymm2) (%_% ymm12) (%_% ymm12) *)
  0xc4; 0xc2; 0x15; 0x28; 0xc5;
                           (* VPMULDQ (%_% ymm0) (%_% ymm13) (%_% ymm13) *)
  0xc4; 0xc2; 0x0d; 0x28; 0xc6;
                           (* VPMULDQ (%_% ymm0) (%_% ymm14) (%_% ymm14) *)
  0xc4; 0x41; 0x7e; 0x16; 0xdb;
                           (* VMOVSHDUP (%_% ymm11) (%_% ymm11) *)
  0xc4; 0x43; 0x25; 0x02; 0xe3; 0xaa;
                           (* VPBLENDD (%_% ymm12) (%_% ymm11) (%_% ymm11) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x35; 0xfa; 0xdc;
                           (* VPSUBD (%_% ymm11) (%_% ymm9) (%_% ymm12) *)
  0xc4; 0x41; 0x35; 0xfe; 0xd9;
                           (* VPADDD (%_% ymm11) (%_% ymm9) (%_% ymm9) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xf5; 0xaa;
                           (* VPBLENDD (%_% ymm14) (%_% ymm13) (%_% ymm13) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x1d; 0xfe; 0xeb;
                           (* VPADDD (%_% ymm13) (%_% ymm12) (%_% ymm11) *)
  0xc4; 0x41; 0x35; 0xfa; 0xe9;
                           (* VPSUBD (%_% ymm13) (%_% ymm9) (%_% ymm9) *)
  0xc5; 0xfd; 0x7f; 0x67; 0x20;
                           (* VMOVDQA (Memop Word256 (%% (rdi,32))) (%_% ymm4) *)
  0xc5; 0xfd; 0x7f; 0xaf; 0xa0; 0x00; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,160))) (%_% ymm5) *)
  0xc5; 0xfd; 0x7f; 0xb7; 0x20; 0x01; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,288))) (%_% ymm6) *)
  0xc5; 0xfd; 0x7f; 0xbf; 0xa0; 0x01; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,416))) (%_% ymm7) *)
  0xc5; 0x7d; 0x7f; 0x87; 0x20; 0x02; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,544))) (%_% ymm8) *)
  0xc5; 0x7d; 0x7f; 0x8f; 0xa0; 0x02; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,672))) (%_% ymm9) *)
  0xc5; 0x7d; 0x7f; 0x97; 0x20; 0x03; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,800))) (%_% ymm10) *)
  0xc5; 0x7d; 0x7f; 0x9f; 0xa0; 0x03; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,928))) (%_% ymm11) *)
  0xc4; 0xe2; 0x7d; 0x58; 0x8e; 0x84; 0x00; 0x00; 0x00;
                           (* VPBROADCASTD (%_% ymm1) (Memop Word128 (%% (rsi,132))) *)
  0xc4; 0xe2; 0x7d; 0x58; 0x96; 0x24; 0x05; 0x00; 0x00;
                           (* VPBROADCASTD (%_% ymm2) (Memop Word128 (%% (rsi,1316))) *)
  0xc5; 0xfd; 0x6f; 0x67; 0x40;
                           (* VMOVDQA (%_% ymm4) (Memop Word256 (%% (rdi,64))) *)
  0xc5; 0xfd; 0x6f; 0xaf; 0xc0; 0x00; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm5) (Memop Word256 (%% (rdi,192))) *)
  0xc5; 0xfd; 0x6f; 0xb7; 0x40; 0x01; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm6) (Memop Word256 (%% (rdi,320))) *)
  0xc5; 0xfd; 0x6f; 0xbf; 0xc0; 0x01; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm7) (Memop Word256 (%% (rdi,448))) *)
  0xc5; 0x7d; 0x6f; 0x87; 0x40; 0x02; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm8) (Memop Word256 (%% (rdi,576))) *)
  0xc5; 0x7d; 0x6f; 0x8f; 0xc0; 0x02; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm9) (Memop Word256 (%% (rdi,704))) *)
  0xc5; 0x7d; 0x6f; 0x97; 0x40; 0x03; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm10) (Memop Word256 (%% (rdi,832))) *)
  0xc5; 0x7d; 0x6f; 0x9f; 0xc0; 0x03; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm11) (Memop Word256 (%% (rdi,960))) *)
  0xc4; 0xc2; 0x3d; 0x28; 0xcd;
                           (* VPMULDQ (%_% ymm1) (%_% ymm8) (%_% ymm13) *)
  0xc4; 0x41; 0x7e; 0x16; 0xc4;
                           (* VMOVSHDUP (%_% ymm8) (%_% ymm12) *)
  0xc4; 0xc2; 0x1d; 0x28; 0xce;
                           (* VPMULDQ (%_% ymm1) (%_% ymm12) (%_% ymm14) *)
  0xc4; 0xc2; 0x3d; 0x28; 0xd0;
                           (* VPMULDQ (%_% ymm2) (%_% ymm8) (%_% ymm8) *)
  0xc4; 0xc2; 0x1d; 0x28; 0xd4;
                           (* VPMULDQ (%_% ymm2) (%_% ymm12) (%_% ymm12) *)
  0xc4; 0xc2; 0x15; 0x28; 0xc5;
                           (* VPMULDQ (%_% ymm0) (%_% ymm13) (%_% ymm13) *)
  0xc4; 0xc2; 0x0d; 0x28; 0xc6;
                           (* VPMULDQ (%_% ymm0) (%_% ymm14) (%_% ymm14) *)
  0xc4; 0x41; 0x7e; 0x16; 0xc0;
                           (* VMOVSHDUP (%_% ymm8) (%_% ymm8) *)
  0xc4; 0x43; 0x3d; 0x02; 0xe0; 0xaa;
                           (* VPBLENDD (%_% ymm12) (%_% ymm8) (%_% ymm8) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x5d; 0xfa; 0xc4;
                           (* VPSUBD (%_% ymm8) (%_% ymm4) (%_% ymm12) *)
  0xc5; 0x5d; 0xfe; 0xc4;  (* VPADDD (%_% ymm8) (%_% ymm4) (%_% ymm4) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xf5; 0xaa;
                           (* VPBLENDD (%_% ymm14) (%_% ymm13) (%_% ymm13) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x1d; 0xfe; 0xe8;
                           (* VPADDD (%_% ymm13) (%_% ymm12) (%_% ymm8) *)
  0xc5; 0x5d; 0xfa; 0xec;  (* VPSUBD (%_% ymm13) (%_% ymm4) (%_% ymm4) *)
  0xc4; 0xc2; 0x35; 0x28; 0xcd;
                           (* VPMULDQ (%_% ymm1) (%_% ymm9) (%_% ymm13) *)
  0xc4; 0x41; 0x7e; 0x16; 0xcc;
                           (* VMOVSHDUP (%_% ymm9) (%_% ymm12) *)
  0xc4; 0xc2; 0x1d; 0x28; 0xce;
                           (* VPMULDQ (%_% ymm1) (%_% ymm12) (%_% ymm14) *)
  0xc4; 0xc2; 0x35; 0x28; 0xd1;
                           (* VPMULDQ (%_% ymm2) (%_% ymm9) (%_% ymm9) *)
  0xc4; 0xc2; 0x1d; 0x28; 0xd4;
                           (* VPMULDQ (%_% ymm2) (%_% ymm12) (%_% ymm12) *)
  0xc4; 0xc2; 0x15; 0x28; 0xc5;
                           (* VPMULDQ (%_% ymm0) (%_% ymm13) (%_% ymm13) *)
  0xc4; 0xc2; 0x0d; 0x28; 0xc6;
                           (* VPMULDQ (%_% ymm0) (%_% ymm14) (%_% ymm14) *)
  0xc4; 0x41; 0x7e; 0x16; 0xc9;
                           (* VMOVSHDUP (%_% ymm9) (%_% ymm9) *)
  0xc4; 0x43; 0x35; 0x02; 0xe1; 0xaa;
                           (* VPBLENDD (%_% ymm12) (%_% ymm9) (%_% ymm9) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x55; 0xfa; 0xcc;
                           (* VPSUBD (%_% ymm9) (%_% ymm5) (%_% ymm12) *)
  0xc5; 0x55; 0xfe; 0xcd;  (* VPADDD (%_% ymm9) (%_% ymm5) (%_% ymm5) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xf5; 0xaa;
                           (* VPBLENDD (%_% ymm14) (%_% ymm13) (%_% ymm13) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x1d; 0xfe; 0xe9;
                           (* VPADDD (%_% ymm13) (%_% ymm12) (%_% ymm9) *)
  0xc5; 0x55; 0xfa; 0xed;  (* VPSUBD (%_% ymm13) (%_% ymm5) (%_% ymm5) *)
  0xc4; 0xc2; 0x2d; 0x28; 0xcd;
                           (* VPMULDQ (%_% ymm1) (%_% ymm10) (%_% ymm13) *)
  0xc4; 0x41; 0x7e; 0x16; 0xd4;
                           (* VMOVSHDUP (%_% ymm10) (%_% ymm12) *)
  0xc4; 0xc2; 0x1d; 0x28; 0xce;
                           (* VPMULDQ (%_% ymm1) (%_% ymm12) (%_% ymm14) *)
  0xc4; 0xc2; 0x2d; 0x28; 0xd2;
                           (* VPMULDQ (%_% ymm2) (%_% ymm10) (%_% ymm10) *)
  0xc4; 0xc2; 0x1d; 0x28; 0xd4;
                           (* VPMULDQ (%_% ymm2) (%_% ymm12) (%_% ymm12) *)
  0xc4; 0xc2; 0x15; 0x28; 0xc5;
                           (* VPMULDQ (%_% ymm0) (%_% ymm13) (%_% ymm13) *)
  0xc4; 0xc2; 0x0d; 0x28; 0xc6;
                           (* VPMULDQ (%_% ymm0) (%_% ymm14) (%_% ymm14) *)
  0xc4; 0x41; 0x7e; 0x16; 0xd2;
                           (* VMOVSHDUP (%_% ymm10) (%_% ymm10) *)
  0xc4; 0x43; 0x2d; 0x02; 0xe2; 0xaa;
                           (* VPBLENDD (%_% ymm12) (%_% ymm10) (%_% ymm10) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x4d; 0xfa; 0xd4;
                           (* VPSUBD (%_% ymm10) (%_% ymm6) (%_% ymm12) *)
  0xc5; 0x4d; 0xfe; 0xd6;  (* VPADDD (%_% ymm10) (%_% ymm6) (%_% ymm6) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xf5; 0xaa;
                           (* VPBLENDD (%_% ymm14) (%_% ymm13) (%_% ymm13) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x1d; 0xfe; 0xea;
                           (* VPADDD (%_% ymm13) (%_% ymm12) (%_% ymm10) *)
  0xc5; 0x4d; 0xfa; 0xee;  (* VPSUBD (%_% ymm13) (%_% ymm6) (%_% ymm6) *)
  0xc4; 0xc2; 0x25; 0x28; 0xcd;
                           (* VPMULDQ (%_% ymm1) (%_% ymm11) (%_% ymm13) *)
  0xc4; 0x41; 0x7e; 0x16; 0xdc;
                           (* VMOVSHDUP (%_% ymm11) (%_% ymm12) *)
  0xc4; 0xc2; 0x1d; 0x28; 0xce;
                           (* VPMULDQ (%_% ymm1) (%_% ymm12) (%_% ymm14) *)
  0xc4; 0xc2; 0x25; 0x28; 0xd3;
                           (* VPMULDQ (%_% ymm2) (%_% ymm11) (%_% ymm11) *)
  0xc4; 0xc2; 0x1d; 0x28; 0xd4;
                           (* VPMULDQ (%_% ymm2) (%_% ymm12) (%_% ymm12) *)
  0xc4; 0xc2; 0x15; 0x28; 0xc5;
                           (* VPMULDQ (%_% ymm0) (%_% ymm13) (%_% ymm13) *)
  0xc4; 0xc2; 0x0d; 0x28; 0xc6;
                           (* VPMULDQ (%_% ymm0) (%_% ymm14) (%_% ymm14) *)
  0xc4; 0x41; 0x7e; 0x16; 0xdb;
                           (* VMOVSHDUP (%_% ymm11) (%_% ymm11) *)
  0xc4; 0x43; 0x25; 0x02; 0xe3; 0xaa;
                           (* VPBLENDD (%_% ymm12) (%_% ymm11) (%_% ymm11) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x45; 0xfa; 0xdc;
                           (* VPSUBD (%_% ymm11) (%_% ymm7) (%_% ymm12) *)
  0xc5; 0x45; 0xfe; 0xdf;  (* VPADDD (%_% ymm11) (%_% ymm7) (%_% ymm7) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xf5; 0xaa;
                           (* VPBLENDD (%_% ymm14) (%_% ymm13) (%_% ymm13) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x1d; 0xfe; 0xeb;
                           (* VPADDD (%_% ymm13) (%_% ymm12) (%_% ymm11) *)
  0xc5; 0x45; 0xfa; 0xef;  (* VPSUBD (%_% ymm13) (%_% ymm7) (%_% ymm7) *)
  0xc4; 0xe2; 0x7d; 0x58; 0x8e; 0x88; 0x00; 0x00; 0x00;
                           (* VPBROADCASTD (%_% ymm1) (Memop Word128 (%% (rsi,136))) *)
  0xc4; 0xe2; 0x7d; 0x58; 0x96; 0x28; 0x05; 0x00; 0x00;
                           (* VPBROADCASTD (%_% ymm2) (Memop Word128 (%% (rsi,1320))) *)
  0xc4; 0xc2; 0x4d; 0x28; 0xcd;
                           (* VPMULDQ (%_% ymm1) (%_% ymm6) (%_% ymm13) *)
  0xc4; 0xc1; 0x7e; 0x16; 0xf4;
                           (* VMOVSHDUP (%_% ymm6) (%_% ymm12) *)
  0xc4; 0xc2; 0x1d; 0x28; 0xce;
                           (* VPMULDQ (%_% ymm1) (%_% ymm12) (%_% ymm14) *)
  0xc4; 0xe2; 0x4d; 0x28; 0xd6;
                           (* VPMULDQ (%_% ymm2) (%_% ymm6) (%_% ymm6) *)
  0xc4; 0xc2; 0x1d; 0x28; 0xd4;
                           (* VPMULDQ (%_% ymm2) (%_% ymm12) (%_% ymm12) *)
  0xc4; 0xc2; 0x15; 0x28; 0xc5;
                           (* VPMULDQ (%_% ymm0) (%_% ymm13) (%_% ymm13) *)
  0xc4; 0xc2; 0x0d; 0x28; 0xc6;
                           (* VPMULDQ (%_% ymm0) (%_% ymm14) (%_% ymm14) *)
  0xc5; 0xfe; 0x16; 0xf6;  (* VMOVSHDUP (%_% ymm6) (%_% ymm6) *)
  0xc4; 0x63; 0x4d; 0x02; 0xe6; 0xaa;
                           (* VPBLENDD (%_% ymm12) (%_% ymm6) (%_% ymm6) (Imm8 (word 170)) *)
  0xc4; 0xc1; 0x5d; 0xfa; 0xf4;
                           (* VPSUBD (%_% ymm6) (%_% ymm4) (%_% ymm12) *)
  0xc5; 0xdd; 0xfe; 0xf4;  (* VPADDD (%_% ymm6) (%_% ymm4) (%_% ymm4) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xf5; 0xaa;
                           (* VPBLENDD (%_% ymm14) (%_% ymm13) (%_% ymm13) (Imm8 (word 170)) *)
  0xc5; 0x1d; 0xfe; 0xee;  (* VPADDD (%_% ymm13) (%_% ymm12) (%_% ymm6) *)
  0xc5; 0x5d; 0xfa; 0xec;  (* VPSUBD (%_% ymm13) (%_% ymm4) (%_% ymm4) *)
  0xc4; 0xc2; 0x45; 0x28; 0xcd;
                           (* VPMULDQ (%_% ymm1) (%_% ymm7) (%_% ymm13) *)
  0xc4; 0xc1; 0x7e; 0x16; 0xfc;
                           (* VMOVSHDUP (%_% ymm7) (%_% ymm12) *)
  0xc4; 0xc2; 0x1d; 0x28; 0xce;
                           (* VPMULDQ (%_% ymm1) (%_% ymm12) (%_% ymm14) *)
  0xc4; 0xe2; 0x45; 0x28; 0xd7;
                           (* VPMULDQ (%_% ymm2) (%_% ymm7) (%_% ymm7) *)
  0xc4; 0xc2; 0x1d; 0x28; 0xd4;
                           (* VPMULDQ (%_% ymm2) (%_% ymm12) (%_% ymm12) *)
  0xc4; 0xc2; 0x15; 0x28; 0xc5;
                           (* VPMULDQ (%_% ymm0) (%_% ymm13) (%_% ymm13) *)
  0xc4; 0xc2; 0x0d; 0x28; 0xc6;
                           (* VPMULDQ (%_% ymm0) (%_% ymm14) (%_% ymm14) *)
  0xc5; 0xfe; 0x16; 0xff;  (* VMOVSHDUP (%_% ymm7) (%_% ymm7) *)
  0xc4; 0x63; 0x45; 0x02; 0xe7; 0xaa;
                           (* VPBLENDD (%_% ymm12) (%_% ymm7) (%_% ymm7) (Imm8 (word 170)) *)
  0xc4; 0xc1; 0x55; 0xfa; 0xfc;
                           (* VPSUBD (%_% ymm7) (%_% ymm5) (%_% ymm12) *)
  0xc5; 0xd5; 0xfe; 0xfd;  (* VPADDD (%_% ymm7) (%_% ymm5) (%_% ymm5) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xf5; 0xaa;
                           (* VPBLENDD (%_% ymm14) (%_% ymm13) (%_% ymm13) (Imm8 (word 170)) *)
  0xc5; 0x1d; 0xfe; 0xef;  (* VPADDD (%_% ymm13) (%_% ymm12) (%_% ymm7) *)
  0xc5; 0x55; 0xfa; 0xed;  (* VPSUBD (%_% ymm13) (%_% ymm5) (%_% ymm5) *)
  0xc4; 0xe2; 0x7d; 0x58; 0x8e; 0x8c; 0x00; 0x00; 0x00;
                           (* VPBROADCASTD (%_% ymm1) (Memop Word128 (%% (rsi,140))) *)
  0xc4; 0xe2; 0x7d; 0x58; 0x96; 0x2c; 0x05; 0x00; 0x00;
                           (* VPBROADCASTD (%_% ymm2) (Memop Word128 (%% (rsi,1324))) *)
  0xc4; 0xc2; 0x2d; 0x28; 0xcd;
                           (* VPMULDQ (%_% ymm1) (%_% ymm10) (%_% ymm13) *)
  0xc4; 0x41; 0x7e; 0x16; 0xd4;
                           (* VMOVSHDUP (%_% ymm10) (%_% ymm12) *)
  0xc4; 0xc2; 0x1d; 0x28; 0xce;
                           (* VPMULDQ (%_% ymm1) (%_% ymm12) (%_% ymm14) *)
  0xc4; 0xc2; 0x2d; 0x28; 0xd2;
                           (* VPMULDQ (%_% ymm2) (%_% ymm10) (%_% ymm10) *)
  0xc4; 0xc2; 0x1d; 0x28; 0xd4;
                           (* VPMULDQ (%_% ymm2) (%_% ymm12) (%_% ymm12) *)
  0xc4; 0xc2; 0x15; 0x28; 0xc5;
                           (* VPMULDQ (%_% ymm0) (%_% ymm13) (%_% ymm13) *)
  0xc4; 0xc2; 0x0d; 0x28; 0xc6;
                           (* VPMULDQ (%_% ymm0) (%_% ymm14) (%_% ymm14) *)
  0xc4; 0x41; 0x7e; 0x16; 0xd2;
                           (* VMOVSHDUP (%_% ymm10) (%_% ymm10) *)
  0xc4; 0x43; 0x2d; 0x02; 0xe2; 0xaa;
                           (* VPBLENDD (%_% ymm12) (%_% ymm10) (%_% ymm10) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x3d; 0xfa; 0xd4;
                           (* VPSUBD (%_% ymm10) (%_% ymm8) (%_% ymm12) *)
  0xc4; 0x41; 0x3d; 0xfe; 0xd0;
                           (* VPADDD (%_% ymm10) (%_% ymm8) (%_% ymm8) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xf5; 0xaa;
                           (* VPBLENDD (%_% ymm14) (%_% ymm13) (%_% ymm13) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x1d; 0xfe; 0xea;
                           (* VPADDD (%_% ymm13) (%_% ymm12) (%_% ymm10) *)
  0xc4; 0x41; 0x3d; 0xfa; 0xe8;
                           (* VPSUBD (%_% ymm13) (%_% ymm8) (%_% ymm8) *)
  0xc4; 0xc2; 0x25; 0x28; 0xcd;
                           (* VPMULDQ (%_% ymm1) (%_% ymm11) (%_% ymm13) *)
  0xc4; 0x41; 0x7e; 0x16; 0xdc;
                           (* VMOVSHDUP (%_% ymm11) (%_% ymm12) *)
  0xc4; 0xc2; 0x1d; 0x28; 0xce;
                           (* VPMULDQ (%_% ymm1) (%_% ymm12) (%_% ymm14) *)
  0xc4; 0xc2; 0x25; 0x28; 0xd3;
                           (* VPMULDQ (%_% ymm2) (%_% ymm11) (%_% ymm11) *)
  0xc4; 0xc2; 0x1d; 0x28; 0xd4;
                           (* VPMULDQ (%_% ymm2) (%_% ymm12) (%_% ymm12) *)
  0xc4; 0xc2; 0x15; 0x28; 0xc5;
                           (* VPMULDQ (%_% ymm0) (%_% ymm13) (%_% ymm13) *)
  0xc4; 0xc2; 0x0d; 0x28; 0xc6;
                           (* VPMULDQ (%_% ymm0) (%_% ymm14) (%_% ymm14) *)
  0xc4; 0x41; 0x7e; 0x16; 0xdb;
                           (* VMOVSHDUP (%_% ymm11) (%_% ymm11) *)
  0xc4; 0x43; 0x25; 0x02; 0xe3; 0xaa;
                           (* VPBLENDD (%_% ymm12) (%_% ymm11) (%_% ymm11) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x35; 0xfa; 0xdc;
                           (* VPSUBD (%_% ymm11) (%_% ymm9) (%_% ymm12) *)
  0xc4; 0x41; 0x35; 0xfe; 0xd9;
                           (* VPADDD (%_% ymm11) (%_% ymm9) (%_% ymm9) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xf5; 0xaa;
                           (* VPBLENDD (%_% ymm14) (%_% ymm13) (%_% ymm13) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x1d; 0xfe; 0xeb;
                           (* VPADDD (%_% ymm13) (%_% ymm12) (%_% ymm11) *)
  0xc4; 0x41; 0x35; 0xfa; 0xe9;
                           (* VPSUBD (%_% ymm13) (%_% ymm9) (%_% ymm9) *)
  0xc5; 0xfd; 0x7f; 0x67; 0x40;
                           (* VMOVDQA (Memop Word256 (%% (rdi,64))) (%_% ymm4) *)
  0xc5; 0xfd; 0x7f; 0xaf; 0xc0; 0x00; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,192))) (%_% ymm5) *)
  0xc5; 0xfd; 0x7f; 0xb7; 0x40; 0x01; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,320))) (%_% ymm6) *)
  0xc5; 0xfd; 0x7f; 0xbf; 0xc0; 0x01; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,448))) (%_% ymm7) *)
  0xc5; 0x7d; 0x7f; 0x87; 0x40; 0x02; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,576))) (%_% ymm8) *)
  0xc5; 0x7d; 0x7f; 0x8f; 0xc0; 0x02; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,704))) (%_% ymm9) *)
  0xc5; 0x7d; 0x7f; 0x97; 0x40; 0x03; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,832))) (%_% ymm10) *)
  0xc5; 0x7d; 0x7f; 0x9f; 0xc0; 0x03; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,960))) (%_% ymm11) *)
  0xc4; 0xe2; 0x7d; 0x58; 0x8e; 0x84; 0x00; 0x00; 0x00;
                           (* VPBROADCASTD (%_% ymm1) (Memop Word128 (%% (rsi,132))) *)
  0xc4; 0xe2; 0x7d; 0x58; 0x96; 0x24; 0x05; 0x00; 0x00;
                           (* VPBROADCASTD (%_% ymm2) (Memop Word128 (%% (rsi,1316))) *)
  0xc5; 0xfd; 0x6f; 0x67; 0x60;
                           (* VMOVDQA (%_% ymm4) (Memop Word256 (%% (rdi,96))) *)
  0xc5; 0xfd; 0x6f; 0xaf; 0xe0; 0x00; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm5) (Memop Word256 (%% (rdi,224))) *)
  0xc5; 0xfd; 0x6f; 0xb7; 0x60; 0x01; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm6) (Memop Word256 (%% (rdi,352))) *)
  0xc5; 0xfd; 0x6f; 0xbf; 0xe0; 0x01; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm7) (Memop Word256 (%% (rdi,480))) *)
  0xc5; 0x7d; 0x6f; 0x87; 0x60; 0x02; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm8) (Memop Word256 (%% (rdi,608))) *)
  0xc5; 0x7d; 0x6f; 0x8f; 0xe0; 0x02; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm9) (Memop Word256 (%% (rdi,736))) *)
  0xc5; 0x7d; 0x6f; 0x97; 0x60; 0x03; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm10) (Memop Word256 (%% (rdi,864))) *)
  0xc5; 0x7d; 0x6f; 0x9f; 0xe0; 0x03; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm11) (Memop Word256 (%% (rdi,992))) *)
  0xc4; 0xc2; 0x3d; 0x28; 0xcd;
                           (* VPMULDQ (%_% ymm1) (%_% ymm8) (%_% ymm13) *)
  0xc4; 0x41; 0x7e; 0x16; 0xc4;
                           (* VMOVSHDUP (%_% ymm8) (%_% ymm12) *)
  0xc4; 0xc2; 0x1d; 0x28; 0xce;
                           (* VPMULDQ (%_% ymm1) (%_% ymm12) (%_% ymm14) *)
  0xc4; 0xc2; 0x3d; 0x28; 0xd0;
                           (* VPMULDQ (%_% ymm2) (%_% ymm8) (%_% ymm8) *)
  0xc4; 0xc2; 0x1d; 0x28; 0xd4;
                           (* VPMULDQ (%_% ymm2) (%_% ymm12) (%_% ymm12) *)
  0xc4; 0xc2; 0x15; 0x28; 0xc5;
                           (* VPMULDQ (%_% ymm0) (%_% ymm13) (%_% ymm13) *)
  0xc4; 0xc2; 0x0d; 0x28; 0xc6;
                           (* VPMULDQ (%_% ymm0) (%_% ymm14) (%_% ymm14) *)
  0xc4; 0x41; 0x7e; 0x16; 0xc0;
                           (* VMOVSHDUP (%_% ymm8) (%_% ymm8) *)
  0xc4; 0x43; 0x3d; 0x02; 0xe0; 0xaa;
                           (* VPBLENDD (%_% ymm12) (%_% ymm8) (%_% ymm8) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x5d; 0xfa; 0xc4;
                           (* VPSUBD (%_% ymm8) (%_% ymm4) (%_% ymm12) *)
  0xc5; 0x5d; 0xfe; 0xc4;  (* VPADDD (%_% ymm8) (%_% ymm4) (%_% ymm4) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xf5; 0xaa;
                           (* VPBLENDD (%_% ymm14) (%_% ymm13) (%_% ymm13) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x1d; 0xfe; 0xe8;
                           (* VPADDD (%_% ymm13) (%_% ymm12) (%_% ymm8) *)
  0xc5; 0x5d; 0xfa; 0xec;  (* VPSUBD (%_% ymm13) (%_% ymm4) (%_% ymm4) *)
  0xc4; 0xc2; 0x35; 0x28; 0xcd;
                           (* VPMULDQ (%_% ymm1) (%_% ymm9) (%_% ymm13) *)
  0xc4; 0x41; 0x7e; 0x16; 0xcc;
                           (* VMOVSHDUP (%_% ymm9) (%_% ymm12) *)
  0xc4; 0xc2; 0x1d; 0x28; 0xce;
                           (* VPMULDQ (%_% ymm1) (%_% ymm12) (%_% ymm14) *)
  0xc4; 0xc2; 0x35; 0x28; 0xd1;
                           (* VPMULDQ (%_% ymm2) (%_% ymm9) (%_% ymm9) *)
  0xc4; 0xc2; 0x1d; 0x28; 0xd4;
                           (* VPMULDQ (%_% ymm2) (%_% ymm12) (%_% ymm12) *)
  0xc4; 0xc2; 0x15; 0x28; 0xc5;
                           (* VPMULDQ (%_% ymm0) (%_% ymm13) (%_% ymm13) *)
  0xc4; 0xc2; 0x0d; 0x28; 0xc6;
                           (* VPMULDQ (%_% ymm0) (%_% ymm14) (%_% ymm14) *)
  0xc4; 0x41; 0x7e; 0x16; 0xc9;
                           (* VMOVSHDUP (%_% ymm9) (%_% ymm9) *)
  0xc4; 0x43; 0x35; 0x02; 0xe1; 0xaa;
                           (* VPBLENDD (%_% ymm12) (%_% ymm9) (%_% ymm9) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x55; 0xfa; 0xcc;
                           (* VPSUBD (%_% ymm9) (%_% ymm5) (%_% ymm12) *)
  0xc5; 0x55; 0xfe; 0xcd;  (* VPADDD (%_% ymm9) (%_% ymm5) (%_% ymm5) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xf5; 0xaa;
                           (* VPBLENDD (%_% ymm14) (%_% ymm13) (%_% ymm13) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x1d; 0xfe; 0xe9;
                           (* VPADDD (%_% ymm13) (%_% ymm12) (%_% ymm9) *)
  0xc5; 0x55; 0xfa; 0xed;  (* VPSUBD (%_% ymm13) (%_% ymm5) (%_% ymm5) *)
  0xc4; 0xc2; 0x2d; 0x28; 0xcd;
                           (* VPMULDQ (%_% ymm1) (%_% ymm10) (%_% ymm13) *)
  0xc4; 0x41; 0x7e; 0x16; 0xd4;
                           (* VMOVSHDUP (%_% ymm10) (%_% ymm12) *)
  0xc4; 0xc2; 0x1d; 0x28; 0xce;
                           (* VPMULDQ (%_% ymm1) (%_% ymm12) (%_% ymm14) *)
  0xc4; 0xc2; 0x2d; 0x28; 0xd2;
                           (* VPMULDQ (%_% ymm2) (%_% ymm10) (%_% ymm10) *)
  0xc4; 0xc2; 0x1d; 0x28; 0xd4;
                           (* VPMULDQ (%_% ymm2) (%_% ymm12) (%_% ymm12) *)
  0xc4; 0xc2; 0x15; 0x28; 0xc5;
                           (* VPMULDQ (%_% ymm0) (%_% ymm13) (%_% ymm13) *)
  0xc4; 0xc2; 0x0d; 0x28; 0xc6;
                           (* VPMULDQ (%_% ymm0) (%_% ymm14) (%_% ymm14) *)
  0xc4; 0x41; 0x7e; 0x16; 0xd2;
                           (* VMOVSHDUP (%_% ymm10) (%_% ymm10) *)
  0xc4; 0x43; 0x2d; 0x02; 0xe2; 0xaa;
                           (* VPBLENDD (%_% ymm12) (%_% ymm10) (%_% ymm10) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x4d; 0xfa; 0xd4;
                           (* VPSUBD (%_% ymm10) (%_% ymm6) (%_% ymm12) *)
  0xc5; 0x4d; 0xfe; 0xd6;  (* VPADDD (%_% ymm10) (%_% ymm6) (%_% ymm6) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xf5; 0xaa;
                           (* VPBLENDD (%_% ymm14) (%_% ymm13) (%_% ymm13) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x1d; 0xfe; 0xea;
                           (* VPADDD (%_% ymm13) (%_% ymm12) (%_% ymm10) *)
  0xc5; 0x4d; 0xfa; 0xee;  (* VPSUBD (%_% ymm13) (%_% ymm6) (%_% ymm6) *)
  0xc4; 0xc2; 0x25; 0x28; 0xcd;
                           (* VPMULDQ (%_% ymm1) (%_% ymm11) (%_% ymm13) *)
  0xc4; 0x41; 0x7e; 0x16; 0xdc;
                           (* VMOVSHDUP (%_% ymm11) (%_% ymm12) *)
  0xc4; 0xc2; 0x1d; 0x28; 0xce;
                           (* VPMULDQ (%_% ymm1) (%_% ymm12) (%_% ymm14) *)
  0xc4; 0xc2; 0x25; 0x28; 0xd3;
                           (* VPMULDQ (%_% ymm2) (%_% ymm11) (%_% ymm11) *)
  0xc4; 0xc2; 0x1d; 0x28; 0xd4;
                           (* VPMULDQ (%_% ymm2) (%_% ymm12) (%_% ymm12) *)
  0xc4; 0xc2; 0x15; 0x28; 0xc5;
                           (* VPMULDQ (%_% ymm0) (%_% ymm13) (%_% ymm13) *)
  0xc4; 0xc2; 0x0d; 0x28; 0xc6;
                           (* VPMULDQ (%_% ymm0) (%_% ymm14) (%_% ymm14) *)
  0xc4; 0x41; 0x7e; 0x16; 0xdb;
                           (* VMOVSHDUP (%_% ymm11) (%_% ymm11) *)
  0xc4; 0x43; 0x25; 0x02; 0xe3; 0xaa;
                           (* VPBLENDD (%_% ymm12) (%_% ymm11) (%_% ymm11) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x45; 0xfa; 0xdc;
                           (* VPSUBD (%_% ymm11) (%_% ymm7) (%_% ymm12) *)
  0xc5; 0x45; 0xfe; 0xdf;  (* VPADDD (%_% ymm11) (%_% ymm7) (%_% ymm7) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xf5; 0xaa;
                           (* VPBLENDD (%_% ymm14) (%_% ymm13) (%_% ymm13) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x1d; 0xfe; 0xeb;
                           (* VPADDD (%_% ymm13) (%_% ymm12) (%_% ymm11) *)
  0xc5; 0x45; 0xfa; 0xef;  (* VPSUBD (%_% ymm13) (%_% ymm7) (%_% ymm7) *)
  0xc4; 0xe2; 0x7d; 0x58; 0x8e; 0x88; 0x00; 0x00; 0x00;
                           (* VPBROADCASTD (%_% ymm1) (Memop Word128 (%% (rsi,136))) *)
  0xc4; 0xe2; 0x7d; 0x58; 0x96; 0x28; 0x05; 0x00; 0x00;
                           (* VPBROADCASTD (%_% ymm2) (Memop Word128 (%% (rsi,1320))) *)
  0xc4; 0xc2; 0x4d; 0x28; 0xcd;
                           (* VPMULDQ (%_% ymm1) (%_% ymm6) (%_% ymm13) *)
  0xc4; 0xc1; 0x7e; 0x16; 0xf4;
                           (* VMOVSHDUP (%_% ymm6) (%_% ymm12) *)
  0xc4; 0xc2; 0x1d; 0x28; 0xce;
                           (* VPMULDQ (%_% ymm1) (%_% ymm12) (%_% ymm14) *)
  0xc4; 0xe2; 0x4d; 0x28; 0xd6;
                           (* VPMULDQ (%_% ymm2) (%_% ymm6) (%_% ymm6) *)
  0xc4; 0xc2; 0x1d; 0x28; 0xd4;
                           (* VPMULDQ (%_% ymm2) (%_% ymm12) (%_% ymm12) *)
  0xc4; 0xc2; 0x15; 0x28; 0xc5;
                           (* VPMULDQ (%_% ymm0) (%_% ymm13) (%_% ymm13) *)
  0xc4; 0xc2; 0x0d; 0x28; 0xc6;
                           (* VPMULDQ (%_% ymm0) (%_% ymm14) (%_% ymm14) *)
  0xc5; 0xfe; 0x16; 0xf6;  (* VMOVSHDUP (%_% ymm6) (%_% ymm6) *)
  0xc4; 0x63; 0x4d; 0x02; 0xe6; 0xaa;
                           (* VPBLENDD (%_% ymm12) (%_% ymm6) (%_% ymm6) (Imm8 (word 170)) *)
  0xc4; 0xc1; 0x5d; 0xfa; 0xf4;
                           (* VPSUBD (%_% ymm6) (%_% ymm4) (%_% ymm12) *)
  0xc5; 0xdd; 0xfe; 0xf4;  (* VPADDD (%_% ymm6) (%_% ymm4) (%_% ymm4) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xf5; 0xaa;
                           (* VPBLENDD (%_% ymm14) (%_% ymm13) (%_% ymm13) (Imm8 (word 170)) *)
  0xc5; 0x1d; 0xfe; 0xee;  (* VPADDD (%_% ymm13) (%_% ymm12) (%_% ymm6) *)
  0xc5; 0x5d; 0xfa; 0xec;  (* VPSUBD (%_% ymm13) (%_% ymm4) (%_% ymm4) *)
  0xc4; 0xc2; 0x45; 0x28; 0xcd;
                           (* VPMULDQ (%_% ymm1) (%_% ymm7) (%_% ymm13) *)
  0xc4; 0xc1; 0x7e; 0x16; 0xfc;
                           (* VMOVSHDUP (%_% ymm7) (%_% ymm12) *)
  0xc4; 0xc2; 0x1d; 0x28; 0xce;
                           (* VPMULDQ (%_% ymm1) (%_% ymm12) (%_% ymm14) *)
  0xc4; 0xe2; 0x45; 0x28; 0xd7;
                           (* VPMULDQ (%_% ymm2) (%_% ymm7) (%_% ymm7) *)
  0xc4; 0xc2; 0x1d; 0x28; 0xd4;
                           (* VPMULDQ (%_% ymm2) (%_% ymm12) (%_% ymm12) *)
  0xc4; 0xc2; 0x15; 0x28; 0xc5;
                           (* VPMULDQ (%_% ymm0) (%_% ymm13) (%_% ymm13) *)
  0xc4; 0xc2; 0x0d; 0x28; 0xc6;
                           (* VPMULDQ (%_% ymm0) (%_% ymm14) (%_% ymm14) *)
  0xc5; 0xfe; 0x16; 0xff;  (* VMOVSHDUP (%_% ymm7) (%_% ymm7) *)
  0xc4; 0x63; 0x45; 0x02; 0xe7; 0xaa;
                           (* VPBLENDD (%_% ymm12) (%_% ymm7) (%_% ymm7) (Imm8 (word 170)) *)
  0xc4; 0xc1; 0x55; 0xfa; 0xfc;
                           (* VPSUBD (%_% ymm7) (%_% ymm5) (%_% ymm12) *)
  0xc5; 0xd5; 0xfe; 0xfd;  (* VPADDD (%_% ymm7) (%_% ymm5) (%_% ymm5) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xf5; 0xaa;
                           (* VPBLENDD (%_% ymm14) (%_% ymm13) (%_% ymm13) (Imm8 (word 170)) *)
  0xc5; 0x1d; 0xfe; 0xef;  (* VPADDD (%_% ymm13) (%_% ymm12) (%_% ymm7) *)
  0xc5; 0x55; 0xfa; 0xed;  (* VPSUBD (%_% ymm13) (%_% ymm5) (%_% ymm5) *)
  0xc4; 0xe2; 0x7d; 0x58; 0x8e; 0x8c; 0x00; 0x00; 0x00;
                           (* VPBROADCASTD (%_% ymm1) (Memop Word128 (%% (rsi,140))) *)
  0xc4; 0xe2; 0x7d; 0x58; 0x96; 0x2c; 0x05; 0x00; 0x00;
                           (* VPBROADCASTD (%_% ymm2) (Memop Word128 (%% (rsi,1324))) *)
  0xc4; 0xc2; 0x2d; 0x28; 0xcd;
                           (* VPMULDQ (%_% ymm1) (%_% ymm10) (%_% ymm13) *)
  0xc4; 0x41; 0x7e; 0x16; 0xd4;
                           (* VMOVSHDUP (%_% ymm10) (%_% ymm12) *)
  0xc4; 0xc2; 0x1d; 0x28; 0xce;
                           (* VPMULDQ (%_% ymm1) (%_% ymm12) (%_% ymm14) *)
  0xc4; 0xc2; 0x2d; 0x28; 0xd2;
                           (* VPMULDQ (%_% ymm2) (%_% ymm10) (%_% ymm10) *)
  0xc4; 0xc2; 0x1d; 0x28; 0xd4;
                           (* VPMULDQ (%_% ymm2) (%_% ymm12) (%_% ymm12) *)
  0xc4; 0xc2; 0x15; 0x28; 0xc5;
                           (* VPMULDQ (%_% ymm0) (%_% ymm13) (%_% ymm13) *)
  0xc4; 0xc2; 0x0d; 0x28; 0xc6;
                           (* VPMULDQ (%_% ymm0) (%_% ymm14) (%_% ymm14) *)
  0xc4; 0x41; 0x7e; 0x16; 0xd2;
                           (* VMOVSHDUP (%_% ymm10) (%_% ymm10) *)
  0xc4; 0x43; 0x2d; 0x02; 0xe2; 0xaa;
                           (* VPBLENDD (%_% ymm12) (%_% ymm10) (%_% ymm10) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x3d; 0xfa; 0xd4;
                           (* VPSUBD (%_% ymm10) (%_% ymm8) (%_% ymm12) *)
  0xc4; 0x41; 0x3d; 0xfe; 0xd0;
                           (* VPADDD (%_% ymm10) (%_% ymm8) (%_% ymm8) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xf5; 0xaa;
                           (* VPBLENDD (%_% ymm14) (%_% ymm13) (%_% ymm13) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x1d; 0xfe; 0xea;
                           (* VPADDD (%_% ymm13) (%_% ymm12) (%_% ymm10) *)
  0xc4; 0x41; 0x3d; 0xfa; 0xe8;
                           (* VPSUBD (%_% ymm13) (%_% ymm8) (%_% ymm8) *)
  0xc4; 0xc2; 0x25; 0x28; 0xcd;
                           (* VPMULDQ (%_% ymm1) (%_% ymm11) (%_% ymm13) *)
  0xc4; 0x41; 0x7e; 0x16; 0xdc;
                           (* VMOVSHDUP (%_% ymm11) (%_% ymm12) *)
  0xc4; 0xc2; 0x1d; 0x28; 0xce;
                           (* VPMULDQ (%_% ymm1) (%_% ymm12) (%_% ymm14) *)
  0xc4; 0xc2; 0x25; 0x28; 0xd3;
                           (* VPMULDQ (%_% ymm2) (%_% ymm11) (%_% ymm11) *)
  0xc4; 0xc2; 0x1d; 0x28; 0xd4;
                           (* VPMULDQ (%_% ymm2) (%_% ymm12) (%_% ymm12) *)
  0xc4; 0xc2; 0x15; 0x28; 0xc5;
                           (* VPMULDQ (%_% ymm0) (%_% ymm13) (%_% ymm13) *)
  0xc4; 0xc2; 0x0d; 0x28; 0xc6;
                           (* VPMULDQ (%_% ymm0) (%_% ymm14) (%_% ymm14) *)
  0xc4; 0x41; 0x7e; 0x16; 0xdb;
                           (* VMOVSHDUP (%_% ymm11) (%_% ymm11) *)
  0xc4; 0x43; 0x25; 0x02; 0xe3; 0xaa;
                           (* VPBLENDD (%_% ymm12) (%_% ymm11) (%_% ymm11) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x35; 0xfa; 0xdc;
                           (* VPSUBD (%_% ymm11) (%_% ymm9) (%_% ymm12) *)
  0xc4; 0x41; 0x35; 0xfe; 0xd9;
                           (* VPADDD (%_% ymm11) (%_% ymm9) (%_% ymm9) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xf5; 0xaa;
                           (* VPBLENDD (%_% ymm14) (%_% ymm13) (%_% ymm13) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x1d; 0xfe; 0xeb;
                           (* VPADDD (%_% ymm13) (%_% ymm12) (%_% ymm11) *)
  0xc4; 0x41; 0x35; 0xfa; 0xe9;
                           (* VPSUBD (%_% ymm13) (%_% ymm9) (%_% ymm9) *)
  0xc5; 0xfd; 0x7f; 0x67; 0x60;
                           (* VMOVDQA (Memop Word256 (%% (rdi,96))) (%_% ymm4) *)
  0xc5; 0xfd; 0x7f; 0xaf; 0xe0; 0x00; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,224))) (%_% ymm5) *)
  0xc5; 0xfd; 0x7f; 0xb7; 0x60; 0x01; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,352))) (%_% ymm6) *)
  0xc5; 0xfd; 0x7f; 0xbf; 0xe0; 0x01; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,480))) (%_% ymm7) *)
  0xc5; 0x7d; 0x7f; 0x87; 0x60; 0x02; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,608))) (%_% ymm8) *)
  0xc5; 0x7d; 0x7f; 0x8f; 0xe0; 0x02; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,736))) (%_% ymm9) *)
  0xc5; 0x7d; 0x7f; 0x97; 0x60; 0x03; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,864))) (%_% ymm10) *)
  0xc5; 0x7d; 0x7f; 0x9f; 0xe0; 0x03; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,992))) (%_% ymm11) *)
  0xc5; 0xfd; 0x6f; 0x27;  (* VMOVDQA (%_% ymm4) (Memop Word256 (%% (rdi,0))) *)
  0xc5; 0xfd; 0x6f; 0x6f; 0x20;
                           (* VMOVDQA (%_% ymm5) (Memop Word256 (%% (rdi,32))) *)
  0xc5; 0xfd; 0x6f; 0x77; 0x40;
                           (* VMOVDQA (%_% ymm6) (Memop Word256 (%% (rdi,64))) *)
  0xc5; 0xfd; 0x6f; 0x7f; 0x60;
                           (* VMOVDQA (%_% ymm7) (Memop Word256 (%% (rdi,96))) *)
  0xc5; 0x7d; 0x6f; 0x87; 0x80; 0x00; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm8) (Memop Word256 (%% (rdi,128))) *)
  0xc5; 0x7d; 0x6f; 0x8f; 0xa0; 0x00; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm9) (Memop Word256 (%% (rdi,160))) *)
  0xc5; 0x7d; 0x6f; 0x97; 0xc0; 0x00; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm10) (Memop Word256 (%% (rdi,192))) *)
  0xc5; 0x7d; 0x6f; 0x9f; 0xe0; 0x00; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm11) (Memop Word256 (%% (rdi,224))) *)
  0xc4; 0xe2; 0x7d; 0x58; 0x8e; 0x90; 0x00; 0x00; 0x00;
                           (* VPBROADCASTD (%_% ymm1) (Memop Word128 (%% (rsi,144))) *)
  0xc4; 0xe2; 0x7d; 0x58; 0x96; 0x30; 0x05; 0x00; 0x00;
                           (* VPBROADCASTD (%_% ymm2) (Memop Word128 (%% (rsi,1328))) *)
  0xc4; 0xc2; 0x3d; 0x28; 0xcd;
                           (* VPMULDQ (%_% ymm1) (%_% ymm8) (%_% ymm13) *)
  0xc4; 0x41; 0x7e; 0x16; 0xc4;
                           (* VMOVSHDUP (%_% ymm8) (%_% ymm12) *)
  0xc4; 0xc2; 0x1d; 0x28; 0xce;
                           (* VPMULDQ (%_% ymm1) (%_% ymm12) (%_% ymm14) *)
  0xc4; 0xc2; 0x3d; 0x28; 0xd0;
                           (* VPMULDQ (%_% ymm2) (%_% ymm8) (%_% ymm8) *)
  0xc4; 0xc2; 0x1d; 0x28; 0xd4;
                           (* VPMULDQ (%_% ymm2) (%_% ymm12) (%_% ymm12) *)
  0xc4; 0xc2; 0x15; 0x28; 0xc5;
                           (* VPMULDQ (%_% ymm0) (%_% ymm13) (%_% ymm13) *)
  0xc4; 0xc2; 0x0d; 0x28; 0xc6;
                           (* VPMULDQ (%_% ymm0) (%_% ymm14) (%_% ymm14) *)
  0xc4; 0x41; 0x7e; 0x16; 0xc0;
                           (* VMOVSHDUP (%_% ymm8) (%_% ymm8) *)
  0xc4; 0x43; 0x3d; 0x02; 0xe0; 0xaa;
                           (* VPBLENDD (%_% ymm12) (%_% ymm8) (%_% ymm8) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x5d; 0xfa; 0xc4;
                           (* VPSUBD (%_% ymm8) (%_% ymm4) (%_% ymm12) *)
  0xc5; 0x5d; 0xfe; 0xc4;  (* VPADDD (%_% ymm8) (%_% ymm4) (%_% ymm4) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xf5; 0xaa;
                           (* VPBLENDD (%_% ymm14) (%_% ymm13) (%_% ymm13) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x1d; 0xfe; 0xe8;
                           (* VPADDD (%_% ymm13) (%_% ymm12) (%_% ymm8) *)
  0xc5; 0x5d; 0xfa; 0xec;  (* VPSUBD (%_% ymm13) (%_% ymm4) (%_% ymm4) *)
  0xc4; 0xc2; 0x35; 0x28; 0xcd;
                           (* VPMULDQ (%_% ymm1) (%_% ymm9) (%_% ymm13) *)
  0xc4; 0x41; 0x7e; 0x16; 0xcc;
                           (* VMOVSHDUP (%_% ymm9) (%_% ymm12) *)
  0xc4; 0xc2; 0x1d; 0x28; 0xce;
                           (* VPMULDQ (%_% ymm1) (%_% ymm12) (%_% ymm14) *)
  0xc4; 0xc2; 0x35; 0x28; 0xd1;
                           (* VPMULDQ (%_% ymm2) (%_% ymm9) (%_% ymm9) *)
  0xc4; 0xc2; 0x1d; 0x28; 0xd4;
                           (* VPMULDQ (%_% ymm2) (%_% ymm12) (%_% ymm12) *)
  0xc4; 0xc2; 0x15; 0x28; 0xc5;
                           (* VPMULDQ (%_% ymm0) (%_% ymm13) (%_% ymm13) *)
  0xc4; 0xc2; 0x0d; 0x28; 0xc6;
                           (* VPMULDQ (%_% ymm0) (%_% ymm14) (%_% ymm14) *)
  0xc4; 0x41; 0x7e; 0x16; 0xc9;
                           (* VMOVSHDUP (%_% ymm9) (%_% ymm9) *)
  0xc4; 0x43; 0x35; 0x02; 0xe1; 0xaa;
                           (* VPBLENDD (%_% ymm12) (%_% ymm9) (%_% ymm9) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x55; 0xfa; 0xcc;
                           (* VPSUBD (%_% ymm9) (%_% ymm5) (%_% ymm12) *)
  0xc5; 0x55; 0xfe; 0xcd;  (* VPADDD (%_% ymm9) (%_% ymm5) (%_% ymm5) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xf5; 0xaa;
                           (* VPBLENDD (%_% ymm14) (%_% ymm13) (%_% ymm13) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x1d; 0xfe; 0xe9;
                           (* VPADDD (%_% ymm13) (%_% ymm12) (%_% ymm9) *)
  0xc5; 0x55; 0xfa; 0xed;  (* VPSUBD (%_% ymm13) (%_% ymm5) (%_% ymm5) *)
  0xc4; 0xc2; 0x2d; 0x28; 0xcd;
                           (* VPMULDQ (%_% ymm1) (%_% ymm10) (%_% ymm13) *)
  0xc4; 0x41; 0x7e; 0x16; 0xd4;
                           (* VMOVSHDUP (%_% ymm10) (%_% ymm12) *)
  0xc4; 0xc2; 0x1d; 0x28; 0xce;
                           (* VPMULDQ (%_% ymm1) (%_% ymm12) (%_% ymm14) *)
  0xc4; 0xc2; 0x2d; 0x28; 0xd2;
                           (* VPMULDQ (%_% ymm2) (%_% ymm10) (%_% ymm10) *)
  0xc4; 0xc2; 0x1d; 0x28; 0xd4;
                           (* VPMULDQ (%_% ymm2) (%_% ymm12) (%_% ymm12) *)
  0xc4; 0xc2; 0x15; 0x28; 0xc5;
                           (* VPMULDQ (%_% ymm0) (%_% ymm13) (%_% ymm13) *)
  0xc4; 0xc2; 0x0d; 0x28; 0xc6;
                           (* VPMULDQ (%_% ymm0) (%_% ymm14) (%_% ymm14) *)
  0xc4; 0x41; 0x7e; 0x16; 0xd2;
                           (* VMOVSHDUP (%_% ymm10) (%_% ymm10) *)
  0xc4; 0x43; 0x2d; 0x02; 0xe2; 0xaa;
                           (* VPBLENDD (%_% ymm12) (%_% ymm10) (%_% ymm10) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x4d; 0xfa; 0xd4;
                           (* VPSUBD (%_% ymm10) (%_% ymm6) (%_% ymm12) *)
  0xc5; 0x4d; 0xfe; 0xd6;  (* VPADDD (%_% ymm10) (%_% ymm6) (%_% ymm6) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xf5; 0xaa;
                           (* VPBLENDD (%_% ymm14) (%_% ymm13) (%_% ymm13) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x1d; 0xfe; 0xea;
                           (* VPADDD (%_% ymm13) (%_% ymm12) (%_% ymm10) *)
  0xc5; 0x4d; 0xfa; 0xee;  (* VPSUBD (%_% ymm13) (%_% ymm6) (%_% ymm6) *)
  0xc4; 0xc2; 0x25; 0x28; 0xcd;
                           (* VPMULDQ (%_% ymm1) (%_% ymm11) (%_% ymm13) *)
  0xc4; 0x41; 0x7e; 0x16; 0xdc;
                           (* VMOVSHDUP (%_% ymm11) (%_% ymm12) *)
  0xc4; 0xc2; 0x1d; 0x28; 0xce;
                           (* VPMULDQ (%_% ymm1) (%_% ymm12) (%_% ymm14) *)
  0xc4; 0xc2; 0x25; 0x28; 0xd3;
                           (* VPMULDQ (%_% ymm2) (%_% ymm11) (%_% ymm11) *)
  0xc4; 0xc2; 0x1d; 0x28; 0xd4;
                           (* VPMULDQ (%_% ymm2) (%_% ymm12) (%_% ymm12) *)
  0xc4; 0xc2; 0x15; 0x28; 0xc5;
                           (* VPMULDQ (%_% ymm0) (%_% ymm13) (%_% ymm13) *)
  0xc4; 0xc2; 0x0d; 0x28; 0xc6;
                           (* VPMULDQ (%_% ymm0) (%_% ymm14) (%_% ymm14) *)
  0xc4; 0x41; 0x7e; 0x16; 0xdb;
                           (* VMOVSHDUP (%_% ymm11) (%_% ymm11) *)
  0xc4; 0x43; 0x25; 0x02; 0xe3; 0xaa;
                           (* VPBLENDD (%_% ymm12) (%_% ymm11) (%_% ymm11) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x45; 0xfa; 0xdc;
                           (* VPSUBD (%_% ymm11) (%_% ymm7) (%_% ymm12) *)
  0xc5; 0x45; 0xfe; 0xdf;  (* VPADDD (%_% ymm11) (%_% ymm7) (%_% ymm7) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xf5; 0xaa;
                           (* VPBLENDD (%_% ymm14) (%_% ymm13) (%_% ymm13) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x1d; 0xfe; 0xeb;
                           (* VPADDD (%_% ymm13) (%_% ymm12) (%_% ymm11) *)
  0xc5; 0x45; 0xfa; 0xef;  (* VPSUBD (%_% ymm13) (%_% ymm7) (%_% ymm7) *)
  0xc4; 0xc3; 0x5d; 0x46; 0xd8; 0x20;
                           (* VPERM2I128 (%_% ymm3) (%_% ymm4) (%_% ymm8) (Imm8 (word 32)) *)
  0xc4; 0x43; 0x5d; 0x46; 0xc0; 0x31;
                           (* VPERM2I128 (%_% ymm8) (%_% ymm4) (%_% ymm8) (Imm8 (word 49)) *)
  0xc4; 0xc3; 0x55; 0x46; 0xe1; 0x20;
                           (* VPERM2I128 (%_% ymm4) (%_% ymm5) (%_% ymm9) (Imm8 (word 32)) *)
  0xc4; 0x43; 0x55; 0x46; 0xc9; 0x31;
                           (* VPERM2I128 (%_% ymm9) (%_% ymm5) (%_% ymm9) (Imm8 (word 49)) *)
  0xc4; 0xc3; 0x4d; 0x46; 0xea; 0x20;
                           (* VPERM2I128 (%_% ymm5) (%_% ymm6) (%_% ymm10) (Imm8 (word 32)) *)
  0xc4; 0x43; 0x4d; 0x46; 0xd2; 0x31;
                           (* VPERM2I128 (%_% ymm10) (%_% ymm6) (%_% ymm10) (Imm8 (word 49)) *)
  0xc4; 0xc3; 0x45; 0x46; 0xf3; 0x20;
                           (* VPERM2I128 (%_% ymm6) (%_% ymm7) (%_% ymm11) (Imm8 (word 32)) *)
  0xc4; 0x43; 0x45; 0x46; 0xdb; 0x31;
                           (* VPERM2I128 (%_% ymm11) (%_% ymm7) (%_% ymm11) (Imm8 (word 49)) *)
  0xc5; 0xfd; 0x6f; 0x8e; 0xa0; 0x00; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm1) (Memop Word256 (%% (rsi,160))) *)
  0xc5; 0xfd; 0x6f; 0x96; 0x40; 0x05; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm2) (Memop Word256 (%% (rsi,1344))) *)
  0xc4; 0xc2; 0x55; 0x28; 0xcd;
                           (* VPMULDQ (%_% ymm1) (%_% ymm5) (%_% ymm13) *)
  0xc4; 0xc1; 0x7e; 0x16; 0xec;
                           (* VMOVSHDUP (%_% ymm5) (%_% ymm12) *)
  0xc4; 0xc2; 0x1d; 0x28; 0xce;
                           (* VPMULDQ (%_% ymm1) (%_% ymm12) (%_% ymm14) *)
  0xc4; 0xe2; 0x55; 0x28; 0xd5;
                           (* VPMULDQ (%_% ymm2) (%_% ymm5) (%_% ymm5) *)
  0xc4; 0xc2; 0x1d; 0x28; 0xd4;
                           (* VPMULDQ (%_% ymm2) (%_% ymm12) (%_% ymm12) *)
  0xc4; 0xc2; 0x15; 0x28; 0xc5;
                           (* VPMULDQ (%_% ymm0) (%_% ymm13) (%_% ymm13) *)
  0xc4; 0xc2; 0x0d; 0x28; 0xc6;
                           (* VPMULDQ (%_% ymm0) (%_% ymm14) (%_% ymm14) *)
  0xc5; 0xfe; 0x16; 0xed;  (* VMOVSHDUP (%_% ymm5) (%_% ymm5) *)
  0xc4; 0x63; 0x55; 0x02; 0xe5; 0xaa;
                           (* VPBLENDD (%_% ymm12) (%_% ymm5) (%_% ymm5) (Imm8 (word 170)) *)
  0xc4; 0xc1; 0x65; 0xfa; 0xec;
                           (* VPSUBD (%_% ymm5) (%_% ymm3) (%_% ymm12) *)
  0xc5; 0xe5; 0xfe; 0xeb;  (* VPADDD (%_% ymm5) (%_% ymm3) (%_% ymm3) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xf5; 0xaa;
                           (* VPBLENDD (%_% ymm14) (%_% ymm13) (%_% ymm13) (Imm8 (word 170)) *)
  0xc5; 0x1d; 0xfe; 0xed;  (* VPADDD (%_% ymm13) (%_% ymm12) (%_% ymm5) *)
  0xc5; 0x65; 0xfa; 0xeb;  (* VPSUBD (%_% ymm13) (%_% ymm3) (%_% ymm3) *)
  0xc4; 0xc2; 0x2d; 0x28; 0xcd;
                           (* VPMULDQ (%_% ymm1) (%_% ymm10) (%_% ymm13) *)
  0xc4; 0x41; 0x7e; 0x16; 0xd4;
                           (* VMOVSHDUP (%_% ymm10) (%_% ymm12) *)
  0xc4; 0xc2; 0x1d; 0x28; 0xce;
                           (* VPMULDQ (%_% ymm1) (%_% ymm12) (%_% ymm14) *)
  0xc4; 0xc2; 0x2d; 0x28; 0xd2;
                           (* VPMULDQ (%_% ymm2) (%_% ymm10) (%_% ymm10) *)
  0xc4; 0xc2; 0x1d; 0x28; 0xd4;
                           (* VPMULDQ (%_% ymm2) (%_% ymm12) (%_% ymm12) *)
  0xc4; 0xc2; 0x15; 0x28; 0xc5;
                           (* VPMULDQ (%_% ymm0) (%_% ymm13) (%_% ymm13) *)
  0xc4; 0xc2; 0x0d; 0x28; 0xc6;
                           (* VPMULDQ (%_% ymm0) (%_% ymm14) (%_% ymm14) *)
  0xc4; 0x41; 0x7e; 0x16; 0xd2;
                           (* VMOVSHDUP (%_% ymm10) (%_% ymm10) *)
  0xc4; 0x43; 0x2d; 0x02; 0xe2; 0xaa;
                           (* VPBLENDD (%_% ymm12) (%_% ymm10) (%_% ymm10) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x3d; 0xfa; 0xd4;
                           (* VPSUBD (%_% ymm10) (%_% ymm8) (%_% ymm12) *)
  0xc4; 0x41; 0x3d; 0xfe; 0xd0;
                           (* VPADDD (%_% ymm10) (%_% ymm8) (%_% ymm8) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xf5; 0xaa;
                           (* VPBLENDD (%_% ymm14) (%_% ymm13) (%_% ymm13) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x1d; 0xfe; 0xea;
                           (* VPADDD (%_% ymm13) (%_% ymm12) (%_% ymm10) *)
  0xc4; 0x41; 0x3d; 0xfa; 0xe8;
                           (* VPSUBD (%_% ymm13) (%_% ymm8) (%_% ymm8) *)
  0xc4; 0xc2; 0x4d; 0x28; 0xcd;
                           (* VPMULDQ (%_% ymm1) (%_% ymm6) (%_% ymm13) *)
  0xc4; 0xc1; 0x7e; 0x16; 0xf4;
                           (* VMOVSHDUP (%_% ymm6) (%_% ymm12) *)
  0xc4; 0xc2; 0x1d; 0x28; 0xce;
                           (* VPMULDQ (%_% ymm1) (%_% ymm12) (%_% ymm14) *)
  0xc4; 0xe2; 0x4d; 0x28; 0xd6;
                           (* VPMULDQ (%_% ymm2) (%_% ymm6) (%_% ymm6) *)
  0xc4; 0xc2; 0x1d; 0x28; 0xd4;
                           (* VPMULDQ (%_% ymm2) (%_% ymm12) (%_% ymm12) *)
  0xc4; 0xc2; 0x15; 0x28; 0xc5;
                           (* VPMULDQ (%_% ymm0) (%_% ymm13) (%_% ymm13) *)
  0xc4; 0xc2; 0x0d; 0x28; 0xc6;
                           (* VPMULDQ (%_% ymm0) (%_% ymm14) (%_% ymm14) *)
  0xc5; 0xfe; 0x16; 0xf6;  (* VMOVSHDUP (%_% ymm6) (%_% ymm6) *)
  0xc4; 0x63; 0x4d; 0x02; 0xe6; 0xaa;
                           (* VPBLENDD (%_% ymm12) (%_% ymm6) (%_% ymm6) (Imm8 (word 170)) *)
  0xc4; 0xc1; 0x5d; 0xfa; 0xf4;
                           (* VPSUBD (%_% ymm6) (%_% ymm4) (%_% ymm12) *)
  0xc5; 0xdd; 0xfe; 0xf4;  (* VPADDD (%_% ymm6) (%_% ymm4) (%_% ymm4) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xf5; 0xaa;
                           (* VPBLENDD (%_% ymm14) (%_% ymm13) (%_% ymm13) (Imm8 (word 170)) *)
  0xc5; 0x1d; 0xfe; 0xee;  (* VPADDD (%_% ymm13) (%_% ymm12) (%_% ymm6) *)
  0xc5; 0x5d; 0xfa; 0xec;  (* VPSUBD (%_% ymm13) (%_% ymm4) (%_% ymm4) *)
  0xc4; 0xc2; 0x25; 0x28; 0xcd;
                           (* VPMULDQ (%_% ymm1) (%_% ymm11) (%_% ymm13) *)
  0xc4; 0x41; 0x7e; 0x16; 0xdc;
                           (* VMOVSHDUP (%_% ymm11) (%_% ymm12) *)
  0xc4; 0xc2; 0x1d; 0x28; 0xce;
                           (* VPMULDQ (%_% ymm1) (%_% ymm12) (%_% ymm14) *)
  0xc4; 0xc2; 0x25; 0x28; 0xd3;
                           (* VPMULDQ (%_% ymm2) (%_% ymm11) (%_% ymm11) *)
  0xc4; 0xc2; 0x1d; 0x28; 0xd4;
                           (* VPMULDQ (%_% ymm2) (%_% ymm12) (%_% ymm12) *)
  0xc4; 0xc2; 0x15; 0x28; 0xc5;
                           (* VPMULDQ (%_% ymm0) (%_% ymm13) (%_% ymm13) *)
  0xc4; 0xc2; 0x0d; 0x28; 0xc6;
                           (* VPMULDQ (%_% ymm0) (%_% ymm14) (%_% ymm14) *)
  0xc4; 0x41; 0x7e; 0x16; 0xdb;
                           (* VMOVSHDUP (%_% ymm11) (%_% ymm11) *)
  0xc4; 0x43; 0x25; 0x02; 0xe3; 0xaa;
                           (* VPBLENDD (%_% ymm12) (%_% ymm11) (%_% ymm11) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x35; 0xfa; 0xdc;
                           (* VPSUBD (%_% ymm11) (%_% ymm9) (%_% ymm12) *)
  0xc4; 0x41; 0x35; 0xfe; 0xd9;
                           (* VPADDD (%_% ymm11) (%_% ymm9) (%_% ymm9) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xf5; 0xaa;
                           (* VPBLENDD (%_% ymm14) (%_% ymm13) (%_% ymm13) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x1d; 0xfe; 0xeb;
                           (* VPADDD (%_% ymm13) (%_% ymm12) (%_% ymm11) *)
  0xc4; 0x41; 0x35; 0xfa; 0xe9;
                           (* VPSUBD (%_% ymm13) (%_% ymm9) (%_% ymm9) *)
  0xc5; 0xe5; 0x6c; 0xfd;  (* VPUNPCKLQDQ (%_% ymm7) (%_% ymm3) (%_% ymm5) *)
  0xc5; 0xe5; 0x6d; 0xed;  (* VPUNPCKHQDQ (%_% ymm5) (%_% ymm3) (%_% ymm5) *)
  0xc4; 0xc1; 0x3d; 0x6c; 0xda;
                           (* VPUNPCKLQDQ (%_% ymm3) (%_% ymm8) (%_% ymm10) *)
  0xc4; 0x41; 0x3d; 0x6d; 0xd2;
                           (* VPUNPCKHQDQ (%_% ymm10) (%_% ymm8) (%_% ymm10) *)
  0xc5; 0x5d; 0x6c; 0xc6;  (* VPUNPCKLQDQ (%_% ymm8) (%_% ymm4) (%_% ymm6) *)
  0xc5; 0xdd; 0x6d; 0xf6;  (* VPUNPCKHQDQ (%_% ymm6) (%_% ymm4) (%_% ymm6) *)
  0xc4; 0xc1; 0x35; 0x6c; 0xe3;
                           (* VPUNPCKLQDQ (%_% ymm4) (%_% ymm9) (%_% ymm11) *)
  0xc4; 0x41; 0x35; 0x6d; 0xdb;
                           (* VPUNPCKHQDQ (%_% ymm11) (%_% ymm9) (%_% ymm11) *)
  0xc5; 0xfd; 0x6f; 0x8e; 0x20; 0x01; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm1) (Memop Word256 (%% (rsi,288))) *)
  0xc5; 0xfd; 0x6f; 0x96; 0xc0; 0x05; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm2) (Memop Word256 (%% (rsi,1472))) *)
  0xc4; 0xc2; 0x3d; 0x28; 0xcd;
                           (* VPMULDQ (%_% ymm1) (%_% ymm8) (%_% ymm13) *)
  0xc4; 0x41; 0x7e; 0x16; 0xc4;
                           (* VMOVSHDUP (%_% ymm8) (%_% ymm12) *)
  0xc4; 0xc2; 0x1d; 0x28; 0xce;
                           (* VPMULDQ (%_% ymm1) (%_% ymm12) (%_% ymm14) *)
  0xc4; 0xc2; 0x3d; 0x28; 0xd0;
                           (* VPMULDQ (%_% ymm2) (%_% ymm8) (%_% ymm8) *)
  0xc4; 0xc2; 0x1d; 0x28; 0xd4;
                           (* VPMULDQ (%_% ymm2) (%_% ymm12) (%_% ymm12) *)
  0xc4; 0xc2; 0x15; 0x28; 0xc5;
                           (* VPMULDQ (%_% ymm0) (%_% ymm13) (%_% ymm13) *)
  0xc4; 0xc2; 0x0d; 0x28; 0xc6;
                           (* VPMULDQ (%_% ymm0) (%_% ymm14) (%_% ymm14) *)
  0xc4; 0x41; 0x7e; 0x16; 0xc0;
                           (* VMOVSHDUP (%_% ymm8) (%_% ymm8) *)
  0xc4; 0x43; 0x3d; 0x02; 0xe0; 0xaa;
                           (* VPBLENDD (%_% ymm12) (%_% ymm8) (%_% ymm8) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x45; 0xfa; 0xc4;
                           (* VPSUBD (%_% ymm8) (%_% ymm7) (%_% ymm12) *)
  0xc5; 0x45; 0xfe; 0xc7;  (* VPADDD (%_% ymm8) (%_% ymm7) (%_% ymm7) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xf5; 0xaa;
                           (* VPBLENDD (%_% ymm14) (%_% ymm13) (%_% ymm13) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x1d; 0xfe; 0xe8;
                           (* VPADDD (%_% ymm13) (%_% ymm12) (%_% ymm8) *)
  0xc5; 0x45; 0xfa; 0xef;  (* VPSUBD (%_% ymm13) (%_% ymm7) (%_% ymm7) *)
  0xc4; 0xc2; 0x4d; 0x28; 0xcd;
                           (* VPMULDQ (%_% ymm1) (%_% ymm6) (%_% ymm13) *)
  0xc4; 0xc1; 0x7e; 0x16; 0xf4;
                           (* VMOVSHDUP (%_% ymm6) (%_% ymm12) *)
  0xc4; 0xc2; 0x1d; 0x28; 0xce;
                           (* VPMULDQ (%_% ymm1) (%_% ymm12) (%_% ymm14) *)
  0xc4; 0xe2; 0x4d; 0x28; 0xd6;
                           (* VPMULDQ (%_% ymm2) (%_% ymm6) (%_% ymm6) *)
  0xc4; 0xc2; 0x1d; 0x28; 0xd4;
                           (* VPMULDQ (%_% ymm2) (%_% ymm12) (%_% ymm12) *)
  0xc4; 0xc2; 0x15; 0x28; 0xc5;
                           (* VPMULDQ (%_% ymm0) (%_% ymm13) (%_% ymm13) *)
  0xc4; 0xc2; 0x0d; 0x28; 0xc6;
                           (* VPMULDQ (%_% ymm0) (%_% ymm14) (%_% ymm14) *)
  0xc5; 0xfe; 0x16; 0xf6;  (* VMOVSHDUP (%_% ymm6) (%_% ymm6) *)
  0xc4; 0x63; 0x4d; 0x02; 0xe6; 0xaa;
                           (* VPBLENDD (%_% ymm12) (%_% ymm6) (%_% ymm6) (Imm8 (word 170)) *)
  0xc4; 0xc1; 0x55; 0xfa; 0xf4;
                           (* VPSUBD (%_% ymm6) (%_% ymm5) (%_% ymm12) *)
  0xc5; 0xd5; 0xfe; 0xf5;  (* VPADDD (%_% ymm6) (%_% ymm5) (%_% ymm5) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xf5; 0xaa;
                           (* VPBLENDD (%_% ymm14) (%_% ymm13) (%_% ymm13) (Imm8 (word 170)) *)
  0xc5; 0x1d; 0xfe; 0xee;  (* VPADDD (%_% ymm13) (%_% ymm12) (%_% ymm6) *)
  0xc5; 0x55; 0xfa; 0xed;  (* VPSUBD (%_% ymm13) (%_% ymm5) (%_% ymm5) *)
  0xc4; 0xc2; 0x5d; 0x28; 0xcd;
                           (* VPMULDQ (%_% ymm1) (%_% ymm4) (%_% ymm13) *)
  0xc4; 0xc1; 0x7e; 0x16; 0xe4;
                           (* VMOVSHDUP (%_% ymm4) (%_% ymm12) *)
  0xc4; 0xc2; 0x1d; 0x28; 0xce;
                           (* VPMULDQ (%_% ymm1) (%_% ymm12) (%_% ymm14) *)
  0xc4; 0xe2; 0x5d; 0x28; 0xd4;
                           (* VPMULDQ (%_% ymm2) (%_% ymm4) (%_% ymm4) *)
  0xc4; 0xc2; 0x1d; 0x28; 0xd4;
                           (* VPMULDQ (%_% ymm2) (%_% ymm12) (%_% ymm12) *)
  0xc4; 0xc2; 0x15; 0x28; 0xc5;
                           (* VPMULDQ (%_% ymm0) (%_% ymm13) (%_% ymm13) *)
  0xc4; 0xc2; 0x0d; 0x28; 0xc6;
                           (* VPMULDQ (%_% ymm0) (%_% ymm14) (%_% ymm14) *)
  0xc5; 0xfe; 0x16; 0xe4;  (* VMOVSHDUP (%_% ymm4) (%_% ymm4) *)
  0xc4; 0x63; 0x5d; 0x02; 0xe4; 0xaa;
                           (* VPBLENDD (%_% ymm12) (%_% ymm4) (%_% ymm4) (Imm8 (word 170)) *)
  0xc4; 0xc1; 0x65; 0xfa; 0xe4;
                           (* VPSUBD (%_% ymm4) (%_% ymm3) (%_% ymm12) *)
  0xc5; 0xe5; 0xfe; 0xe3;  (* VPADDD (%_% ymm4) (%_% ymm3) (%_% ymm3) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xf5; 0xaa;
                           (* VPBLENDD (%_% ymm14) (%_% ymm13) (%_% ymm13) (Imm8 (word 170)) *)
  0xc5; 0x1d; 0xfe; 0xec;  (* VPADDD (%_% ymm13) (%_% ymm12) (%_% ymm4) *)
  0xc5; 0x65; 0xfa; 0xeb;  (* VPSUBD (%_% ymm13) (%_% ymm3) (%_% ymm3) *)
  0xc4; 0xc2; 0x25; 0x28; 0xcd;
                           (* VPMULDQ (%_% ymm1) (%_% ymm11) (%_% ymm13) *)
  0xc4; 0x41; 0x7e; 0x16; 0xdc;
                           (* VMOVSHDUP (%_% ymm11) (%_% ymm12) *)
  0xc4; 0xc2; 0x1d; 0x28; 0xce;
                           (* VPMULDQ (%_% ymm1) (%_% ymm12) (%_% ymm14) *)
  0xc4; 0xc2; 0x25; 0x28; 0xd3;
                           (* VPMULDQ (%_% ymm2) (%_% ymm11) (%_% ymm11) *)
  0xc4; 0xc2; 0x1d; 0x28; 0xd4;
                           (* VPMULDQ (%_% ymm2) (%_% ymm12) (%_% ymm12) *)
  0xc4; 0xc2; 0x15; 0x28; 0xc5;
                           (* VPMULDQ (%_% ymm0) (%_% ymm13) (%_% ymm13) *)
  0xc4; 0xc2; 0x0d; 0x28; 0xc6;
                           (* VPMULDQ (%_% ymm0) (%_% ymm14) (%_% ymm14) *)
  0xc4; 0x41; 0x7e; 0x16; 0xdb;
                           (* VMOVSHDUP (%_% ymm11) (%_% ymm11) *)
  0xc4; 0x43; 0x25; 0x02; 0xe3; 0xaa;
                           (* VPBLENDD (%_% ymm12) (%_% ymm11) (%_% ymm11) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x2d; 0xfa; 0xdc;
                           (* VPSUBD (%_% ymm11) (%_% ymm10) (%_% ymm12) *)
  0xc4; 0x41; 0x2d; 0xfe; 0xda;
                           (* VPADDD (%_% ymm11) (%_% ymm10) (%_% ymm10) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xf5; 0xaa;
                           (* VPBLENDD (%_% ymm14) (%_% ymm13) (%_% ymm13) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x1d; 0xfe; 0xeb;
                           (* VPADDD (%_% ymm13) (%_% ymm12) (%_% ymm11) *)
  0xc4; 0x41; 0x2d; 0xfa; 0xea;
                           (* VPSUBD (%_% ymm13) (%_% ymm10) (%_% ymm10) *)
  0xc4; 0x41; 0x7e; 0x12; 0xc8;
                           (* VMOVSLDUP (%_% ymm9) (%_% ymm8) *)
  0xc4; 0x63; 0x35; 0x02; 0xcf; 0xaa;
                           (* VPBLENDD (%_% ymm9) (%_% ymm9) (%_% ymm7) (Imm8 (word 170)) *)
  0xc5; 0xc5; 0x73; 0xd7; 0x20;
                           (* VPSRLQ (%_% ymm7) (%_% ymm7) (Imm8 (word 32)) *)
  0xc4; 0x63; 0x3d; 0x02; 0xc7; 0xaa;
                           (* VPBLENDD (%_% ymm8) (%_% ymm8) (%_% ymm7) (Imm8 (word 170)) *)
  0xc5; 0xfe; 0x12; 0xfe;  (* VMOVSLDUP (%_% ymm7) (%_% ymm6) *)
  0xc4; 0xe3; 0x45; 0x02; 0xfd; 0xaa;
                           (* VPBLENDD (%_% ymm7) (%_% ymm7) (%_% ymm5) (Imm8 (word 170)) *)
  0xc5; 0xd5; 0x73; 0xd5; 0x20;
                           (* VPSRLQ (%_% ymm5) (%_% ymm5) (Imm8 (word 32)) *)
  0xc4; 0xe3; 0x4d; 0x02; 0xf5; 0xaa;
                           (* VPBLENDD (%_% ymm6) (%_% ymm6) (%_% ymm5) (Imm8 (word 170)) *)
  0xc5; 0xfe; 0x12; 0xec;  (* VMOVSLDUP (%_% ymm5) (%_% ymm4) *)
  0xc4; 0xe3; 0x55; 0x02; 0xeb; 0xaa;
                           (* VPBLENDD (%_% ymm5) (%_% ymm5) (%_% ymm3) (Imm8 (word 170)) *)
  0xc5; 0xe5; 0x73; 0xd3; 0x20;
                           (* VPSRLQ (%_% ymm3) (%_% ymm3) (Imm8 (word 32)) *)
  0xc4; 0xe3; 0x5d; 0x02; 0xe3; 0xaa;
                           (* VPBLENDD (%_% ymm4) (%_% ymm4) (%_% ymm3) (Imm8 (word 170)) *)
  0xc4; 0xc1; 0x7e; 0x12; 0xdb;
                           (* VMOVSLDUP (%_% ymm3) (%_% ymm11) *)
  0xc4; 0xc3; 0x65; 0x02; 0xda; 0xaa;
                           (* VPBLENDD (%_% ymm3) (%_% ymm3) (%_% ymm10) (Imm8 (word 170)) *)
  0xc4; 0xc1; 0x2d; 0x73; 0xd2; 0x20;
                           (* VPSRLQ (%_% ymm10) (%_% ymm10) (Imm8 (word 32)) *)
  0xc4; 0x43; 0x25; 0x02; 0xda; 0xaa;
                           (* VPBLENDD (%_% ymm11) (%_% ymm11) (%_% ymm10) (Imm8 (word 170)) *)
  0xc5; 0xfd; 0x6f; 0x8e; 0xa0; 0x01; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm1) (Memop Word256 (%% (rsi,416))) *)
  0xc5; 0xfd; 0x6f; 0x96; 0x40; 0x06; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm2) (Memop Word256 (%% (rsi,1600))) *)
  0xc4; 0xc1; 0x75; 0x73; 0xd2; 0x20;
                           (* VPSRLQ (%_% ymm1) (%_% ymm10) (Imm8 (word 32)) *)
  0xc4; 0xc1; 0x7e; 0x16; 0xd7;
                           (* VMOVSHDUP (%_% ymm2) (%_% ymm15) *)
  0xc4; 0xc2; 0x55; 0x28; 0xcd;
                           (* VPMULDQ (%_% ymm1) (%_% ymm5) (%_% ymm13) *)
  0xc4; 0xc1; 0x7e; 0x16; 0xec;
                           (* VMOVSHDUP (%_% ymm5) (%_% ymm12) *)
  0xc4; 0x42; 0x1d; 0x28; 0xd6;
                           (* VPMULDQ (%_% ymm10) (%_% ymm12) (%_% ymm14) *)
  0xc4; 0xe2; 0x55; 0x28; 0xd5;
                           (* VPMULDQ (%_% ymm2) (%_% ymm5) (%_% ymm5) *)
  0xc4; 0x42; 0x1d; 0x28; 0xfc;
                           (* VPMULDQ (%_% ymm15) (%_% ymm12) (%_% ymm12) *)
  0xc4; 0xc2; 0x15; 0x28; 0xc5;
                           (* VPMULDQ (%_% ymm0) (%_% ymm13) (%_% ymm13) *)
  0xc4; 0xc2; 0x0d; 0x28; 0xc6;
                           (* VPMULDQ (%_% ymm0) (%_% ymm14) (%_% ymm14) *)
  0xc5; 0xfe; 0x16; 0xed;  (* VMOVSHDUP (%_% ymm5) (%_% ymm5) *)
  0xc4; 0x63; 0x55; 0x02; 0xe5; 0xaa;
                           (* VPBLENDD (%_% ymm12) (%_% ymm5) (%_% ymm5) (Imm8 (word 170)) *)
  0xc4; 0xc1; 0x35; 0xfa; 0xec;
                           (* VPSUBD (%_% ymm5) (%_% ymm9) (%_% ymm12) *)
  0xc4; 0xc1; 0x35; 0xfe; 0xe9;
                           (* VPADDD (%_% ymm5) (%_% ymm9) (%_% ymm9) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xf5; 0xaa;
                           (* VPBLENDD (%_% ymm14) (%_% ymm13) (%_% ymm13) (Imm8 (word 170)) *)
  0xc5; 0x1d; 0xfe; 0xed;  (* VPADDD (%_% ymm13) (%_% ymm12) (%_% ymm5) *)
  0xc4; 0x41; 0x35; 0xfa; 0xe9;
                           (* VPSUBD (%_% ymm13) (%_% ymm9) (%_% ymm9) *)
  0xc4; 0xc2; 0x5d; 0x28; 0xcd;
                           (* VPMULDQ (%_% ymm1) (%_% ymm4) (%_% ymm13) *)
  0xc4; 0xc1; 0x7e; 0x16; 0xe4;
                           (* VMOVSHDUP (%_% ymm4) (%_% ymm12) *)
  0xc4; 0x42; 0x1d; 0x28; 0xd6;
                           (* VPMULDQ (%_% ymm10) (%_% ymm12) (%_% ymm14) *)
  0xc4; 0xe2; 0x5d; 0x28; 0xd4;
                           (* VPMULDQ (%_% ymm2) (%_% ymm4) (%_% ymm4) *)
  0xc4; 0x42; 0x1d; 0x28; 0xfc;
                           (* VPMULDQ (%_% ymm15) (%_% ymm12) (%_% ymm12) *)
  0xc4; 0xc2; 0x15; 0x28; 0xc5;
                           (* VPMULDQ (%_% ymm0) (%_% ymm13) (%_% ymm13) *)
  0xc4; 0xc2; 0x0d; 0x28; 0xc6;
                           (* VPMULDQ (%_% ymm0) (%_% ymm14) (%_% ymm14) *)
  0xc5; 0xfe; 0x16; 0xe4;  (* VMOVSHDUP (%_% ymm4) (%_% ymm4) *)
  0xc4; 0x63; 0x5d; 0x02; 0xe4; 0xaa;
                           (* VPBLENDD (%_% ymm12) (%_% ymm4) (%_% ymm4) (Imm8 (word 170)) *)
  0xc4; 0xc1; 0x3d; 0xfa; 0xe4;
                           (* VPSUBD (%_% ymm4) (%_% ymm8) (%_% ymm12) *)
  0xc4; 0xc1; 0x3d; 0xfe; 0xe0;
                           (* VPADDD (%_% ymm4) (%_% ymm8) (%_% ymm8) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xf5; 0xaa;
                           (* VPBLENDD (%_% ymm14) (%_% ymm13) (%_% ymm13) (Imm8 (word 170)) *)
  0xc5; 0x1d; 0xfe; 0xec;  (* VPADDD (%_% ymm13) (%_% ymm12) (%_% ymm4) *)
  0xc4; 0x41; 0x3d; 0xfa; 0xe8;
                           (* VPSUBD (%_% ymm13) (%_% ymm8) (%_% ymm8) *)
  0xc4; 0xc2; 0x65; 0x28; 0xcd;
                           (* VPMULDQ (%_% ymm1) (%_% ymm3) (%_% ymm13) *)
  0xc4; 0xc1; 0x7e; 0x16; 0xdc;
                           (* VMOVSHDUP (%_% ymm3) (%_% ymm12) *)
  0xc4; 0x42; 0x1d; 0x28; 0xd6;
                           (* VPMULDQ (%_% ymm10) (%_% ymm12) (%_% ymm14) *)
  0xc4; 0xe2; 0x65; 0x28; 0xd3;
                           (* VPMULDQ (%_% ymm2) (%_% ymm3) (%_% ymm3) *)
  0xc4; 0x42; 0x1d; 0x28; 0xfc;
                           (* VPMULDQ (%_% ymm15) (%_% ymm12) (%_% ymm12) *)
  0xc4; 0xc2; 0x15; 0x28; 0xc5;
                           (* VPMULDQ (%_% ymm0) (%_% ymm13) (%_% ymm13) *)
  0xc4; 0xc2; 0x0d; 0x28; 0xc6;
                           (* VPMULDQ (%_% ymm0) (%_% ymm14) (%_% ymm14) *)
  0xc5; 0xfe; 0x16; 0xdb;  (* VMOVSHDUP (%_% ymm3) (%_% ymm3) *)
  0xc4; 0x63; 0x65; 0x02; 0xe3; 0xaa;
                           (* VPBLENDD (%_% ymm12) (%_% ymm3) (%_% ymm3) (Imm8 (word 170)) *)
  0xc4; 0xc1; 0x45; 0xfa; 0xdc;
                           (* VPSUBD (%_% ymm3) (%_% ymm7) (%_% ymm12) *)
  0xc5; 0xc5; 0xfe; 0xdf;  (* VPADDD (%_% ymm3) (%_% ymm7) (%_% ymm7) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xf5; 0xaa;
                           (* VPBLENDD (%_% ymm14) (%_% ymm13) (%_% ymm13) (Imm8 (word 170)) *)
  0xc5; 0x1d; 0xfe; 0xeb;  (* VPADDD (%_% ymm13) (%_% ymm12) (%_% ymm3) *)
  0xc5; 0x45; 0xfa; 0xef;  (* VPSUBD (%_% ymm13) (%_% ymm7) (%_% ymm7) *)
  0xc4; 0xc2; 0x25; 0x28; 0xcd;
                           (* VPMULDQ (%_% ymm1) (%_% ymm11) (%_% ymm13) *)
  0xc4; 0x41; 0x7e; 0x16; 0xdc;
                           (* VMOVSHDUP (%_% ymm11) (%_% ymm12) *)
  0xc4; 0x42; 0x1d; 0x28; 0xd6;
                           (* VPMULDQ (%_% ymm10) (%_% ymm12) (%_% ymm14) *)
  0xc4; 0xc2; 0x25; 0x28; 0xd3;
                           (* VPMULDQ (%_% ymm2) (%_% ymm11) (%_% ymm11) *)
  0xc4; 0x42; 0x1d; 0x28; 0xfc;
                           (* VPMULDQ (%_% ymm15) (%_% ymm12) (%_% ymm12) *)
  0xc4; 0xc2; 0x15; 0x28; 0xc5;
                           (* VPMULDQ (%_% ymm0) (%_% ymm13) (%_% ymm13) *)
  0xc4; 0xc2; 0x0d; 0x28; 0xc6;
                           (* VPMULDQ (%_% ymm0) (%_% ymm14) (%_% ymm14) *)
  0xc4; 0x41; 0x7e; 0x16; 0xdb;
                           (* VMOVSHDUP (%_% ymm11) (%_% ymm11) *)
  0xc4; 0x43; 0x25; 0x02; 0xe3; 0xaa;
                           (* VPBLENDD (%_% ymm12) (%_% ymm11) (%_% ymm11) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x4d; 0xfa; 0xdc;
                           (* VPSUBD (%_% ymm11) (%_% ymm6) (%_% ymm12) *)
  0xc5; 0x4d; 0xfe; 0xde;  (* VPADDD (%_% ymm11) (%_% ymm6) (%_% ymm6) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xf5; 0xaa;
                           (* VPBLENDD (%_% ymm14) (%_% ymm13) (%_% ymm13) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x1d; 0xfe; 0xeb;
                           (* VPADDD (%_% ymm13) (%_% ymm12) (%_% ymm11) *)
  0xc5; 0x4d; 0xfa; 0xee;  (* VPSUBD (%_% ymm13) (%_% ymm6) (%_% ymm6) *)
  0xc5; 0xfd; 0x6f; 0x8e; 0x20; 0x02; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm1) (Memop Word256 (%% (rsi,544))) *)
  0xc5; 0xfd; 0x6f; 0x96; 0xc0; 0x06; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm2) (Memop Word256 (%% (rsi,1728))) *)
  0xc4; 0xc1; 0x75; 0x73; 0xd2; 0x20;
                           (* VPSRLQ (%_% ymm1) (%_% ymm10) (Imm8 (word 32)) *)
  0xc4; 0xc1; 0x7e; 0x16; 0xd7;
                           (* VMOVSHDUP (%_% ymm2) (%_% ymm15) *)
  0xc4; 0xc2; 0x45; 0x28; 0xcd;
                           (* VPMULDQ (%_% ymm1) (%_% ymm7) (%_% ymm13) *)
  0xc4; 0xc1; 0x7e; 0x16; 0xfc;
                           (* VMOVSHDUP (%_% ymm7) (%_% ymm12) *)
  0xc4; 0x42; 0x1d; 0x28; 0xd6;
                           (* VPMULDQ (%_% ymm10) (%_% ymm12) (%_% ymm14) *)
  0xc4; 0xe2; 0x45; 0x28; 0xd7;
                           (* VPMULDQ (%_% ymm2) (%_% ymm7) (%_% ymm7) *)
  0xc4; 0x42; 0x1d; 0x28; 0xfc;
                           (* VPMULDQ (%_% ymm15) (%_% ymm12) (%_% ymm12) *)
  0xc4; 0xc2; 0x15; 0x28; 0xc5;
                           (* VPMULDQ (%_% ymm0) (%_% ymm13) (%_% ymm13) *)
  0xc4; 0xc2; 0x0d; 0x28; 0xc6;
                           (* VPMULDQ (%_% ymm0) (%_% ymm14) (%_% ymm14) *)
  0xc5; 0xfe; 0x16; 0xff;  (* VMOVSHDUP (%_% ymm7) (%_% ymm7) *)
  0xc4; 0x63; 0x45; 0x02; 0xe7; 0xaa;
                           (* VPBLENDD (%_% ymm12) (%_% ymm7) (%_% ymm7) (Imm8 (word 170)) *)
  0xc4; 0xc1; 0x35; 0xfa; 0xfc;
                           (* VPSUBD (%_% ymm7) (%_% ymm9) (%_% ymm12) *)
  0xc4; 0xc1; 0x35; 0xfe; 0xf9;
                           (* VPADDD (%_% ymm7) (%_% ymm9) (%_% ymm9) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xf5; 0xaa;
                           (* VPBLENDD (%_% ymm14) (%_% ymm13) (%_% ymm13) (Imm8 (word 170)) *)
  0xc5; 0x1d; 0xfe; 0xef;  (* VPADDD (%_% ymm13) (%_% ymm12) (%_% ymm7) *)
  0xc4; 0x41; 0x35; 0xfa; 0xe9;
                           (* VPSUBD (%_% ymm13) (%_% ymm9) (%_% ymm9) *)
  0xc4; 0xc2; 0x4d; 0x28; 0xcd;
                           (* VPMULDQ (%_% ymm1) (%_% ymm6) (%_% ymm13) *)
  0xc4; 0xc1; 0x7e; 0x16; 0xf4;
                           (* VMOVSHDUP (%_% ymm6) (%_% ymm12) *)
  0xc4; 0x42; 0x1d; 0x28; 0xd6;
                           (* VPMULDQ (%_% ymm10) (%_% ymm12) (%_% ymm14) *)
  0xc4; 0xe2; 0x4d; 0x28; 0xd6;
                           (* VPMULDQ (%_% ymm2) (%_% ymm6) (%_% ymm6) *)
  0xc4; 0x42; 0x1d; 0x28; 0xfc;
                           (* VPMULDQ (%_% ymm15) (%_% ymm12) (%_% ymm12) *)
  0xc4; 0xc2; 0x15; 0x28; 0xc5;
                           (* VPMULDQ (%_% ymm0) (%_% ymm13) (%_% ymm13) *)
  0xc4; 0xc2; 0x0d; 0x28; 0xc6;
                           (* VPMULDQ (%_% ymm0) (%_% ymm14) (%_% ymm14) *)
  0xc5; 0xfe; 0x16; 0xf6;  (* VMOVSHDUP (%_% ymm6) (%_% ymm6) *)
  0xc4; 0x63; 0x4d; 0x02; 0xe6; 0xaa;
                           (* VPBLENDD (%_% ymm12) (%_% ymm6) (%_% ymm6) (Imm8 (word 170)) *)
  0xc4; 0xc1; 0x3d; 0xfa; 0xf4;
                           (* VPSUBD (%_% ymm6) (%_% ymm8) (%_% ymm12) *)
  0xc4; 0xc1; 0x3d; 0xfe; 0xf0;
                           (* VPADDD (%_% ymm6) (%_% ymm8) (%_% ymm8) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xf5; 0xaa;
                           (* VPBLENDD (%_% ymm14) (%_% ymm13) (%_% ymm13) (Imm8 (word 170)) *)
  0xc5; 0x1d; 0xfe; 0xee;  (* VPADDD (%_% ymm13) (%_% ymm12) (%_% ymm6) *)
  0xc4; 0x41; 0x3d; 0xfa; 0xe8;
                           (* VPSUBD (%_% ymm13) (%_% ymm8) (%_% ymm8) *)
  0xc5; 0xfd; 0x6f; 0x8e; 0xa0; 0x02; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm1) (Memop Word256 (%% (rsi,672))) *)
  0xc5; 0xfd; 0x6f; 0x96; 0x40; 0x07; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm2) (Memop Word256 (%% (rsi,1856))) *)
  0xc4; 0xc1; 0x75; 0x73; 0xd2; 0x20;
                           (* VPSRLQ (%_% ymm1) (%_% ymm10) (Imm8 (word 32)) *)
  0xc4; 0xc1; 0x7e; 0x16; 0xd7;
                           (* VMOVSHDUP (%_% ymm2) (%_% ymm15) *)
  0xc4; 0xc2; 0x65; 0x28; 0xcd;
                           (* VPMULDQ (%_% ymm1) (%_% ymm3) (%_% ymm13) *)
  0xc4; 0xc1; 0x7e; 0x16; 0xdc;
                           (* VMOVSHDUP (%_% ymm3) (%_% ymm12) *)
  0xc4; 0x42; 0x1d; 0x28; 0xd6;
                           (* VPMULDQ (%_% ymm10) (%_% ymm12) (%_% ymm14) *)
  0xc4; 0xe2; 0x65; 0x28; 0xd3;
                           (* VPMULDQ (%_% ymm2) (%_% ymm3) (%_% ymm3) *)
  0xc4; 0x42; 0x1d; 0x28; 0xfc;
                           (* VPMULDQ (%_% ymm15) (%_% ymm12) (%_% ymm12) *)
  0xc4; 0xc2; 0x15; 0x28; 0xc5;
                           (* VPMULDQ (%_% ymm0) (%_% ymm13) (%_% ymm13) *)
  0xc4; 0xc2; 0x0d; 0x28; 0xc6;
                           (* VPMULDQ (%_% ymm0) (%_% ymm14) (%_% ymm14) *)
  0xc5; 0xfe; 0x16; 0xdb;  (* VMOVSHDUP (%_% ymm3) (%_% ymm3) *)
  0xc4; 0x63; 0x65; 0x02; 0xe3; 0xaa;
                           (* VPBLENDD (%_% ymm12) (%_% ymm3) (%_% ymm3) (Imm8 (word 170)) *)
  0xc4; 0xc1; 0x55; 0xfa; 0xdc;
                           (* VPSUBD (%_% ymm3) (%_% ymm5) (%_% ymm12) *)
  0xc5; 0xd5; 0xfe; 0xdd;  (* VPADDD (%_% ymm3) (%_% ymm5) (%_% ymm5) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xf5; 0xaa;
                           (* VPBLENDD (%_% ymm14) (%_% ymm13) (%_% ymm13) (Imm8 (word 170)) *)
  0xc5; 0x1d; 0xfe; 0xeb;  (* VPADDD (%_% ymm13) (%_% ymm12) (%_% ymm3) *)
  0xc5; 0x55; 0xfa; 0xed;  (* VPSUBD (%_% ymm13) (%_% ymm5) (%_% ymm5) *)
  0xc4; 0xc2; 0x25; 0x28; 0xcd;
                           (* VPMULDQ (%_% ymm1) (%_% ymm11) (%_% ymm13) *)
  0xc4; 0x41; 0x7e; 0x16; 0xdc;
                           (* VMOVSHDUP (%_% ymm11) (%_% ymm12) *)
  0xc4; 0x42; 0x1d; 0x28; 0xd6;
                           (* VPMULDQ (%_% ymm10) (%_% ymm12) (%_% ymm14) *)
  0xc4; 0xc2; 0x25; 0x28; 0xd3;
                           (* VPMULDQ (%_% ymm2) (%_% ymm11) (%_% ymm11) *)
  0xc4; 0x42; 0x1d; 0x28; 0xfc;
                           (* VPMULDQ (%_% ymm15) (%_% ymm12) (%_% ymm12) *)
  0xc4; 0xc2; 0x15; 0x28; 0xc5;
                           (* VPMULDQ (%_% ymm0) (%_% ymm13) (%_% ymm13) *)
  0xc4; 0xc2; 0x0d; 0x28; 0xc6;
                           (* VPMULDQ (%_% ymm0) (%_% ymm14) (%_% ymm14) *)
  0xc4; 0x41; 0x7e; 0x16; 0xdb;
                           (* VMOVSHDUP (%_% ymm11) (%_% ymm11) *)
  0xc4; 0x43; 0x25; 0x02; 0xe3; 0xaa;
                           (* VPBLENDD (%_% ymm12) (%_% ymm11) (%_% ymm11) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x5d; 0xfa; 0xdc;
                           (* VPSUBD (%_% ymm11) (%_% ymm4) (%_% ymm12) *)
  0xc5; 0x5d; 0xfe; 0xdc;  (* VPADDD (%_% ymm11) (%_% ymm4) (%_% ymm4) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xf5; 0xaa;
                           (* VPBLENDD (%_% ymm14) (%_% ymm13) (%_% ymm13) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x1d; 0xfe; 0xeb;
                           (* VPADDD (%_% ymm13) (%_% ymm12) (%_% ymm11) *)
  0xc5; 0x5d; 0xfa; 0xec;  (* VPSUBD (%_% ymm13) (%_% ymm4) (%_% ymm4) *)
  0xc5; 0xfd; 0x6f; 0x8e; 0x20; 0x03; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm1) (Memop Word256 (%% (rsi,800))) *)
  0xc5; 0xfd; 0x6f; 0x96; 0xc0; 0x07; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm2) (Memop Word256 (%% (rsi,1984))) *)
  0xc4; 0xc1; 0x75; 0x73; 0xd2; 0x20;
                           (* VPSRLQ (%_% ymm1) (%_% ymm10) (Imm8 (word 32)) *)
  0xc4; 0xc1; 0x7e; 0x16; 0xd7;
                           (* VMOVSHDUP (%_% ymm2) (%_% ymm15) *)
  0xc4; 0xc2; 0x3d; 0x28; 0xcd;
                           (* VPMULDQ (%_% ymm1) (%_% ymm8) (%_% ymm13) *)
  0xc4; 0x41; 0x7e; 0x16; 0xc4;
                           (* VMOVSHDUP (%_% ymm8) (%_% ymm12) *)
  0xc4; 0x42; 0x1d; 0x28; 0xd6;
                           (* VPMULDQ (%_% ymm10) (%_% ymm12) (%_% ymm14) *)
  0xc4; 0xc2; 0x3d; 0x28; 0xd0;
                           (* VPMULDQ (%_% ymm2) (%_% ymm8) (%_% ymm8) *)
  0xc4; 0x42; 0x1d; 0x28; 0xfc;
                           (* VPMULDQ (%_% ymm15) (%_% ymm12) (%_% ymm12) *)
  0xc4; 0xc2; 0x15; 0x28; 0xc5;
                           (* VPMULDQ (%_% ymm0) (%_% ymm13) (%_% ymm13) *)
  0xc4; 0xc2; 0x0d; 0x28; 0xc6;
                           (* VPMULDQ (%_% ymm0) (%_% ymm14) (%_% ymm14) *)
  0xc4; 0x41; 0x7e; 0x16; 0xc0;
                           (* VMOVSHDUP (%_% ymm8) (%_% ymm8) *)
  0xc4; 0x43; 0x3d; 0x02; 0xe0; 0xaa;
                           (* VPBLENDD (%_% ymm12) (%_% ymm8) (%_% ymm8) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x35; 0xfa; 0xc4;
                           (* VPSUBD (%_% ymm8) (%_% ymm9) (%_% ymm12) *)
  0xc4; 0x41; 0x35; 0xfe; 0xc1;
                           (* VPADDD (%_% ymm8) (%_% ymm9) (%_% ymm9) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xf5; 0xaa;
                           (* VPBLENDD (%_% ymm14) (%_% ymm13) (%_% ymm13) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x1d; 0xfe; 0xe8;
                           (* VPADDD (%_% ymm13) (%_% ymm12) (%_% ymm8) *)
  0xc4; 0x41; 0x35; 0xfa; 0xe9;
                           (* VPSUBD (%_% ymm13) (%_% ymm9) (%_% ymm9) *)
  0xc5; 0xfd; 0x6f; 0x8e; 0xa0; 0x03; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm1) (Memop Word256 (%% (rsi,928))) *)
  0xc5; 0xfd; 0x6f; 0x96; 0x40; 0x08; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm2) (Memop Word256 (%% (rsi,2112))) *)
  0xc4; 0xc1; 0x75; 0x73; 0xd2; 0x20;
                           (* VPSRLQ (%_% ymm1) (%_% ymm10) (Imm8 (word 32)) *)
  0xc4; 0xc1; 0x7e; 0x16; 0xd7;
                           (* VMOVSHDUP (%_% ymm2) (%_% ymm15) *)
  0xc4; 0xc2; 0x4d; 0x28; 0xcd;
                           (* VPMULDQ (%_% ymm1) (%_% ymm6) (%_% ymm13) *)
  0xc4; 0xc1; 0x7e; 0x16; 0xf4;
                           (* VMOVSHDUP (%_% ymm6) (%_% ymm12) *)
  0xc4; 0x42; 0x1d; 0x28; 0xd6;
                           (* VPMULDQ (%_% ymm10) (%_% ymm12) (%_% ymm14) *)
  0xc4; 0xe2; 0x4d; 0x28; 0xd6;
                           (* VPMULDQ (%_% ymm2) (%_% ymm6) (%_% ymm6) *)
  0xc4; 0x42; 0x1d; 0x28; 0xfc;
                           (* VPMULDQ (%_% ymm15) (%_% ymm12) (%_% ymm12) *)
  0xc4; 0xc2; 0x15; 0x28; 0xc5;
                           (* VPMULDQ (%_% ymm0) (%_% ymm13) (%_% ymm13) *)
  0xc4; 0xc2; 0x0d; 0x28; 0xc6;
                           (* VPMULDQ (%_% ymm0) (%_% ymm14) (%_% ymm14) *)
  0xc5; 0xfe; 0x16; 0xf6;  (* VMOVSHDUP (%_% ymm6) (%_% ymm6) *)
  0xc4; 0x63; 0x4d; 0x02; 0xe6; 0xaa;
                           (* VPBLENDD (%_% ymm12) (%_% ymm6) (%_% ymm6) (Imm8 (word 170)) *)
  0xc4; 0xc1; 0x45; 0xfa; 0xf4;
                           (* VPSUBD (%_% ymm6) (%_% ymm7) (%_% ymm12) *)
  0xc5; 0xc5; 0xfe; 0xf7;  (* VPADDD (%_% ymm6) (%_% ymm7) (%_% ymm7) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xf5; 0xaa;
                           (* VPBLENDD (%_% ymm14) (%_% ymm13) (%_% ymm13) (Imm8 (word 170)) *)
  0xc5; 0x1d; 0xfe; 0xee;  (* VPADDD (%_% ymm13) (%_% ymm12) (%_% ymm6) *)
  0xc5; 0x45; 0xfa; 0xef;  (* VPSUBD (%_% ymm13) (%_% ymm7) (%_% ymm7) *)
  0xc5; 0xfd; 0x6f; 0x8e; 0x20; 0x04; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm1) (Memop Word256 (%% (rsi,1056))) *)
  0xc5; 0xfd; 0x6f; 0x96; 0xc0; 0x08; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm2) (Memop Word256 (%% (rsi,2240))) *)
  0xc4; 0xc1; 0x75; 0x73; 0xd2; 0x20;
                           (* VPSRLQ (%_% ymm1) (%_% ymm10) (Imm8 (word 32)) *)
  0xc4; 0xc1; 0x7e; 0x16; 0xd7;
                           (* VMOVSHDUP (%_% ymm2) (%_% ymm15) *)
  0xc4; 0xc2; 0x5d; 0x28; 0xcd;
                           (* VPMULDQ (%_% ymm1) (%_% ymm4) (%_% ymm13) *)
  0xc4; 0xc1; 0x7e; 0x16; 0xe4;
                           (* VMOVSHDUP (%_% ymm4) (%_% ymm12) *)
  0xc4; 0x42; 0x1d; 0x28; 0xd6;
                           (* VPMULDQ (%_% ymm10) (%_% ymm12) (%_% ymm14) *)
  0xc4; 0xe2; 0x5d; 0x28; 0xd4;
                           (* VPMULDQ (%_% ymm2) (%_% ymm4) (%_% ymm4) *)
  0xc4; 0x42; 0x1d; 0x28; 0xfc;
                           (* VPMULDQ (%_% ymm15) (%_% ymm12) (%_% ymm12) *)
  0xc4; 0xc2; 0x15; 0x28; 0xc5;
                           (* VPMULDQ (%_% ymm0) (%_% ymm13) (%_% ymm13) *)
  0xc4; 0xc2; 0x0d; 0x28; 0xc6;
                           (* VPMULDQ (%_% ymm0) (%_% ymm14) (%_% ymm14) *)
  0xc5; 0xfe; 0x16; 0xe4;  (* VMOVSHDUP (%_% ymm4) (%_% ymm4) *)
  0xc4; 0x63; 0x5d; 0x02; 0xe4; 0xaa;
                           (* VPBLENDD (%_% ymm12) (%_% ymm4) (%_% ymm4) (Imm8 (word 170)) *)
  0xc4; 0xc1; 0x55; 0xfa; 0xe4;
                           (* VPSUBD (%_% ymm4) (%_% ymm5) (%_% ymm12) *)
  0xc5; 0xd5; 0xfe; 0xe5;  (* VPADDD (%_% ymm4) (%_% ymm5) (%_% ymm5) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xf5; 0xaa;
                           (* VPBLENDD (%_% ymm14) (%_% ymm13) (%_% ymm13) (Imm8 (word 170)) *)
  0xc5; 0x1d; 0xfe; 0xec;  (* VPADDD (%_% ymm13) (%_% ymm12) (%_% ymm4) *)
  0xc5; 0x55; 0xfa; 0xed;  (* VPSUBD (%_% ymm13) (%_% ymm5) (%_% ymm5) *)
  0xc5; 0xfd; 0x6f; 0x8e; 0xa0; 0x04; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm1) (Memop Word256 (%% (rsi,1184))) *)
  0xc5; 0xfd; 0x6f; 0x96; 0x40; 0x09; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm2) (Memop Word256 (%% (rsi,2368))) *)
  0xc4; 0xc1; 0x75; 0x73; 0xd2; 0x20;
                           (* VPSRLQ (%_% ymm1) (%_% ymm10) (Imm8 (word 32)) *)
  0xc4; 0xc1; 0x7e; 0x16; 0xd7;
                           (* VMOVSHDUP (%_% ymm2) (%_% ymm15) *)
  0xc4; 0xc2; 0x25; 0x28; 0xcd;
                           (* VPMULDQ (%_% ymm1) (%_% ymm11) (%_% ymm13) *)
  0xc4; 0x41; 0x7e; 0x16; 0xdc;
                           (* VMOVSHDUP (%_% ymm11) (%_% ymm12) *)
  0xc4; 0x42; 0x1d; 0x28; 0xd6;
                           (* VPMULDQ (%_% ymm10) (%_% ymm12) (%_% ymm14) *)
  0xc4; 0xc2; 0x25; 0x28; 0xd3;
                           (* VPMULDQ (%_% ymm2) (%_% ymm11) (%_% ymm11) *)
  0xc4; 0x42; 0x1d; 0x28; 0xfc;
                           (* VPMULDQ (%_% ymm15) (%_% ymm12) (%_% ymm12) *)
  0xc4; 0xc2; 0x15; 0x28; 0xc5;
                           (* VPMULDQ (%_% ymm0) (%_% ymm13) (%_% ymm13) *)
  0xc4; 0xc2; 0x0d; 0x28; 0xc6;
                           (* VPMULDQ (%_% ymm0) (%_% ymm14) (%_% ymm14) *)
  0xc4; 0x41; 0x7e; 0x16; 0xdb;
                           (* VMOVSHDUP (%_% ymm11) (%_% ymm11) *)
  0xc4; 0x43; 0x25; 0x02; 0xe3; 0xaa;
                           (* VPBLENDD (%_% ymm12) (%_% ymm11) (%_% ymm11) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x65; 0xfa; 0xdc;
                           (* VPSUBD (%_% ymm11) (%_% ymm3) (%_% ymm12) *)
  0xc5; 0x65; 0xfe; 0xdb;  (* VPADDD (%_% ymm11) (%_% ymm3) (%_% ymm3) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xf5; 0xaa;
                           (* VPBLENDD (%_% ymm14) (%_% ymm13) (%_% ymm13) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x1d; 0xfe; 0xeb;
                           (* VPADDD (%_% ymm13) (%_% ymm12) (%_% ymm11) *)
  0xc5; 0x65; 0xfa; 0xeb;  (* VPSUBD (%_% ymm13) (%_% ymm3) (%_% ymm3) *)
  0xc5; 0x7d; 0x7f; 0x0f;  (* VMOVDQA (Memop Word256 (%% (rdi,0))) (%_% ymm9) *)
  0xc5; 0x7d; 0x7f; 0x47; 0x20;
                           (* VMOVDQA (Memop Word256 (%% (rdi,32))) (%_% ymm8) *)
  0xc5; 0xfd; 0x7f; 0x7f; 0x40;
                           (* VMOVDQA (Memop Word256 (%% (rdi,64))) (%_% ymm7) *)
  0xc5; 0xfd; 0x7f; 0x77; 0x60;
                           (* VMOVDQA (Memop Word256 (%% (rdi,96))) (%_% ymm6) *)
  0xc5; 0xfd; 0x7f; 0xaf; 0x80; 0x00; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,128))) (%_% ymm5) *)
  0xc5; 0xfd; 0x7f; 0xa7; 0xa0; 0x00; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,160))) (%_% ymm4) *)
  0xc5; 0xfd; 0x7f; 0x9f; 0xc0; 0x00; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,192))) (%_% ymm3) *)
  0xc5; 0x7d; 0x7f; 0x9f; 0xe0; 0x00; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,224))) (%_% ymm11) *)
  0xc5; 0xfd; 0x6f; 0xa7; 0x00; 0x01; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm4) (Memop Word256 (%% (rdi,256))) *)
  0xc5; 0xfd; 0x6f; 0xaf; 0x20; 0x01; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm5) (Memop Word256 (%% (rdi,288))) *)
  0xc5; 0xfd; 0x6f; 0xb7; 0x40; 0x01; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm6) (Memop Word256 (%% (rdi,320))) *)
  0xc5; 0xfd; 0x6f; 0xbf; 0x60; 0x01; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm7) (Memop Word256 (%% (rdi,352))) *)
  0xc5; 0x7d; 0x6f; 0x87; 0x80; 0x01; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm8) (Memop Word256 (%% (rdi,384))) *)
  0xc5; 0x7d; 0x6f; 0x8f; 0xa0; 0x01; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm9) (Memop Word256 (%% (rdi,416))) *)
  0xc5; 0x7d; 0x6f; 0x97; 0xc0; 0x01; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm10) (Memop Word256 (%% (rdi,448))) *)
  0xc5; 0x7d; 0x6f; 0x9f; 0xe0; 0x01; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm11) (Memop Word256 (%% (rdi,480))) *)
  0xc4; 0xe2; 0x7d; 0x58; 0x8e; 0x94; 0x00; 0x00; 0x00;
                           (* VPBROADCASTD (%_% ymm1) (Memop Word128 (%% (rsi,148))) *)
  0xc4; 0xe2; 0x7d; 0x58; 0x96; 0x34; 0x05; 0x00; 0x00;
                           (* VPBROADCASTD (%_% ymm2) (Memop Word128 (%% (rsi,1332))) *)
  0xc4; 0xc2; 0x3d; 0x28; 0xcd;
                           (* VPMULDQ (%_% ymm1) (%_% ymm8) (%_% ymm13) *)
  0xc4; 0x41; 0x7e; 0x16; 0xc4;
                           (* VMOVSHDUP (%_% ymm8) (%_% ymm12) *)
  0xc4; 0xc2; 0x1d; 0x28; 0xce;
                           (* VPMULDQ (%_% ymm1) (%_% ymm12) (%_% ymm14) *)
  0xc4; 0xc2; 0x3d; 0x28; 0xd0;
                           (* VPMULDQ (%_% ymm2) (%_% ymm8) (%_% ymm8) *)
  0xc4; 0xc2; 0x1d; 0x28; 0xd4;
                           (* VPMULDQ (%_% ymm2) (%_% ymm12) (%_% ymm12) *)
  0xc4; 0xc2; 0x15; 0x28; 0xc5;
                           (* VPMULDQ (%_% ymm0) (%_% ymm13) (%_% ymm13) *)
  0xc4; 0xc2; 0x0d; 0x28; 0xc6;
                           (* VPMULDQ (%_% ymm0) (%_% ymm14) (%_% ymm14) *)
  0xc4; 0x41; 0x7e; 0x16; 0xc0;
                           (* VMOVSHDUP (%_% ymm8) (%_% ymm8) *)
  0xc4; 0x43; 0x3d; 0x02; 0xe0; 0xaa;
                           (* VPBLENDD (%_% ymm12) (%_% ymm8) (%_% ymm8) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x5d; 0xfa; 0xc4;
                           (* VPSUBD (%_% ymm8) (%_% ymm4) (%_% ymm12) *)
  0xc5; 0x5d; 0xfe; 0xc4;  (* VPADDD (%_% ymm8) (%_% ymm4) (%_% ymm4) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xf5; 0xaa;
                           (* VPBLENDD (%_% ymm14) (%_% ymm13) (%_% ymm13) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x1d; 0xfe; 0xe8;
                           (* VPADDD (%_% ymm13) (%_% ymm12) (%_% ymm8) *)
  0xc5; 0x5d; 0xfa; 0xec;  (* VPSUBD (%_% ymm13) (%_% ymm4) (%_% ymm4) *)
  0xc4; 0xc2; 0x35; 0x28; 0xcd;
                           (* VPMULDQ (%_% ymm1) (%_% ymm9) (%_% ymm13) *)
  0xc4; 0x41; 0x7e; 0x16; 0xcc;
                           (* VMOVSHDUP (%_% ymm9) (%_% ymm12) *)
  0xc4; 0xc2; 0x1d; 0x28; 0xce;
                           (* VPMULDQ (%_% ymm1) (%_% ymm12) (%_% ymm14) *)
  0xc4; 0xc2; 0x35; 0x28; 0xd1;
                           (* VPMULDQ (%_% ymm2) (%_% ymm9) (%_% ymm9) *)
  0xc4; 0xc2; 0x1d; 0x28; 0xd4;
                           (* VPMULDQ (%_% ymm2) (%_% ymm12) (%_% ymm12) *)
  0xc4; 0xc2; 0x15; 0x28; 0xc5;
                           (* VPMULDQ (%_% ymm0) (%_% ymm13) (%_% ymm13) *)
  0xc4; 0xc2; 0x0d; 0x28; 0xc6;
                           (* VPMULDQ (%_% ymm0) (%_% ymm14) (%_% ymm14) *)
  0xc4; 0x41; 0x7e; 0x16; 0xc9;
                           (* VMOVSHDUP (%_% ymm9) (%_% ymm9) *)
  0xc4; 0x43; 0x35; 0x02; 0xe1; 0xaa;
                           (* VPBLENDD (%_% ymm12) (%_% ymm9) (%_% ymm9) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x55; 0xfa; 0xcc;
                           (* VPSUBD (%_% ymm9) (%_% ymm5) (%_% ymm12) *)
  0xc5; 0x55; 0xfe; 0xcd;  (* VPADDD (%_% ymm9) (%_% ymm5) (%_% ymm5) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xf5; 0xaa;
                           (* VPBLENDD (%_% ymm14) (%_% ymm13) (%_% ymm13) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x1d; 0xfe; 0xe9;
                           (* VPADDD (%_% ymm13) (%_% ymm12) (%_% ymm9) *)
  0xc5; 0x55; 0xfa; 0xed;  (* VPSUBD (%_% ymm13) (%_% ymm5) (%_% ymm5) *)
  0xc4; 0xc2; 0x2d; 0x28; 0xcd;
                           (* VPMULDQ (%_% ymm1) (%_% ymm10) (%_% ymm13) *)
  0xc4; 0x41; 0x7e; 0x16; 0xd4;
                           (* VMOVSHDUP (%_% ymm10) (%_% ymm12) *)
  0xc4; 0xc2; 0x1d; 0x28; 0xce;
                           (* VPMULDQ (%_% ymm1) (%_% ymm12) (%_% ymm14) *)
  0xc4; 0xc2; 0x2d; 0x28; 0xd2;
                           (* VPMULDQ (%_% ymm2) (%_% ymm10) (%_% ymm10) *)
  0xc4; 0xc2; 0x1d; 0x28; 0xd4;
                           (* VPMULDQ (%_% ymm2) (%_% ymm12) (%_% ymm12) *)
  0xc4; 0xc2; 0x15; 0x28; 0xc5;
                           (* VPMULDQ (%_% ymm0) (%_% ymm13) (%_% ymm13) *)
  0xc4; 0xc2; 0x0d; 0x28; 0xc6;
                           (* VPMULDQ (%_% ymm0) (%_% ymm14) (%_% ymm14) *)
  0xc4; 0x41; 0x7e; 0x16; 0xd2;
                           (* VMOVSHDUP (%_% ymm10) (%_% ymm10) *)
  0xc4; 0x43; 0x2d; 0x02; 0xe2; 0xaa;
                           (* VPBLENDD (%_% ymm12) (%_% ymm10) (%_% ymm10) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x4d; 0xfa; 0xd4;
                           (* VPSUBD (%_% ymm10) (%_% ymm6) (%_% ymm12) *)
  0xc5; 0x4d; 0xfe; 0xd6;  (* VPADDD (%_% ymm10) (%_% ymm6) (%_% ymm6) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xf5; 0xaa;
                           (* VPBLENDD (%_% ymm14) (%_% ymm13) (%_% ymm13) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x1d; 0xfe; 0xea;
                           (* VPADDD (%_% ymm13) (%_% ymm12) (%_% ymm10) *)
  0xc5; 0x4d; 0xfa; 0xee;  (* VPSUBD (%_% ymm13) (%_% ymm6) (%_% ymm6) *)
  0xc4; 0xc2; 0x25; 0x28; 0xcd;
                           (* VPMULDQ (%_% ymm1) (%_% ymm11) (%_% ymm13) *)
  0xc4; 0x41; 0x7e; 0x16; 0xdc;
                           (* VMOVSHDUP (%_% ymm11) (%_% ymm12) *)
  0xc4; 0xc2; 0x1d; 0x28; 0xce;
                           (* VPMULDQ (%_% ymm1) (%_% ymm12) (%_% ymm14) *)
  0xc4; 0xc2; 0x25; 0x28; 0xd3;
                           (* VPMULDQ (%_% ymm2) (%_% ymm11) (%_% ymm11) *)
  0xc4; 0xc2; 0x1d; 0x28; 0xd4;
                           (* VPMULDQ (%_% ymm2) (%_% ymm12) (%_% ymm12) *)
  0xc4; 0xc2; 0x15; 0x28; 0xc5;
                           (* VPMULDQ (%_% ymm0) (%_% ymm13) (%_% ymm13) *)
  0xc4; 0xc2; 0x0d; 0x28; 0xc6;
                           (* VPMULDQ (%_% ymm0) (%_% ymm14) (%_% ymm14) *)
  0xc4; 0x41; 0x7e; 0x16; 0xdb;
                           (* VMOVSHDUP (%_% ymm11) (%_% ymm11) *)
  0xc4; 0x43; 0x25; 0x02; 0xe3; 0xaa;
                           (* VPBLENDD (%_% ymm12) (%_% ymm11) (%_% ymm11) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x45; 0xfa; 0xdc;
                           (* VPSUBD (%_% ymm11) (%_% ymm7) (%_% ymm12) *)
  0xc5; 0x45; 0xfe; 0xdf;  (* VPADDD (%_% ymm11) (%_% ymm7) (%_% ymm7) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xf5; 0xaa;
                           (* VPBLENDD (%_% ymm14) (%_% ymm13) (%_% ymm13) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x1d; 0xfe; 0xeb;
                           (* VPADDD (%_% ymm13) (%_% ymm12) (%_% ymm11) *)
  0xc5; 0x45; 0xfa; 0xef;  (* VPSUBD (%_% ymm13) (%_% ymm7) (%_% ymm7) *)
  0xc4; 0xc3; 0x5d; 0x46; 0xd8; 0x20;
                           (* VPERM2I128 (%_% ymm3) (%_% ymm4) (%_% ymm8) (Imm8 (word 32)) *)
  0xc4; 0x43; 0x5d; 0x46; 0xc0; 0x31;
                           (* VPERM2I128 (%_% ymm8) (%_% ymm4) (%_% ymm8) (Imm8 (word 49)) *)
  0xc4; 0xc3; 0x55; 0x46; 0xe1; 0x20;
                           (* VPERM2I128 (%_% ymm4) (%_% ymm5) (%_% ymm9) (Imm8 (word 32)) *)
  0xc4; 0x43; 0x55; 0x46; 0xc9; 0x31;
                           (* VPERM2I128 (%_% ymm9) (%_% ymm5) (%_% ymm9) (Imm8 (word 49)) *)
  0xc4; 0xc3; 0x4d; 0x46; 0xea; 0x20;
                           (* VPERM2I128 (%_% ymm5) (%_% ymm6) (%_% ymm10) (Imm8 (word 32)) *)
  0xc4; 0x43; 0x4d; 0x46; 0xd2; 0x31;
                           (* VPERM2I128 (%_% ymm10) (%_% ymm6) (%_% ymm10) (Imm8 (word 49)) *)
  0xc4; 0xc3; 0x45; 0x46; 0xf3; 0x20;
                           (* VPERM2I128 (%_% ymm6) (%_% ymm7) (%_% ymm11) (Imm8 (word 32)) *)
  0xc4; 0x43; 0x45; 0x46; 0xdb; 0x31;
                           (* VPERM2I128 (%_% ymm11) (%_% ymm7) (%_% ymm11) (Imm8 (word 49)) *)
  0xc5; 0xfd; 0x6f; 0x8e; 0xc0; 0x00; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm1) (Memop Word256 (%% (rsi,192))) *)
  0xc5; 0xfd; 0x6f; 0x96; 0x60; 0x05; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm2) (Memop Word256 (%% (rsi,1376))) *)
  0xc4; 0xc2; 0x55; 0x28; 0xcd;
                           (* VPMULDQ (%_% ymm1) (%_% ymm5) (%_% ymm13) *)
  0xc4; 0xc1; 0x7e; 0x16; 0xec;
                           (* VMOVSHDUP (%_% ymm5) (%_% ymm12) *)
  0xc4; 0xc2; 0x1d; 0x28; 0xce;
                           (* VPMULDQ (%_% ymm1) (%_% ymm12) (%_% ymm14) *)
  0xc4; 0xe2; 0x55; 0x28; 0xd5;
                           (* VPMULDQ (%_% ymm2) (%_% ymm5) (%_% ymm5) *)
  0xc4; 0xc2; 0x1d; 0x28; 0xd4;
                           (* VPMULDQ (%_% ymm2) (%_% ymm12) (%_% ymm12) *)
  0xc4; 0xc2; 0x15; 0x28; 0xc5;
                           (* VPMULDQ (%_% ymm0) (%_% ymm13) (%_% ymm13) *)
  0xc4; 0xc2; 0x0d; 0x28; 0xc6;
                           (* VPMULDQ (%_% ymm0) (%_% ymm14) (%_% ymm14) *)
  0xc5; 0xfe; 0x16; 0xed;  (* VMOVSHDUP (%_% ymm5) (%_% ymm5) *)
  0xc4; 0x63; 0x55; 0x02; 0xe5; 0xaa;
                           (* VPBLENDD (%_% ymm12) (%_% ymm5) (%_% ymm5) (Imm8 (word 170)) *)
  0xc4; 0xc1; 0x65; 0xfa; 0xec;
                           (* VPSUBD (%_% ymm5) (%_% ymm3) (%_% ymm12) *)
  0xc5; 0xe5; 0xfe; 0xeb;  (* VPADDD (%_% ymm5) (%_% ymm3) (%_% ymm3) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xf5; 0xaa;
                           (* VPBLENDD (%_% ymm14) (%_% ymm13) (%_% ymm13) (Imm8 (word 170)) *)
  0xc5; 0x1d; 0xfe; 0xed;  (* VPADDD (%_% ymm13) (%_% ymm12) (%_% ymm5) *)
  0xc5; 0x65; 0xfa; 0xeb;  (* VPSUBD (%_% ymm13) (%_% ymm3) (%_% ymm3) *)
  0xc4; 0xc2; 0x2d; 0x28; 0xcd;
                           (* VPMULDQ (%_% ymm1) (%_% ymm10) (%_% ymm13) *)
  0xc4; 0x41; 0x7e; 0x16; 0xd4;
                           (* VMOVSHDUP (%_% ymm10) (%_% ymm12) *)
  0xc4; 0xc2; 0x1d; 0x28; 0xce;
                           (* VPMULDQ (%_% ymm1) (%_% ymm12) (%_% ymm14) *)
  0xc4; 0xc2; 0x2d; 0x28; 0xd2;
                           (* VPMULDQ (%_% ymm2) (%_% ymm10) (%_% ymm10) *)
  0xc4; 0xc2; 0x1d; 0x28; 0xd4;
                           (* VPMULDQ (%_% ymm2) (%_% ymm12) (%_% ymm12) *)
  0xc4; 0xc2; 0x15; 0x28; 0xc5;
                           (* VPMULDQ (%_% ymm0) (%_% ymm13) (%_% ymm13) *)
  0xc4; 0xc2; 0x0d; 0x28; 0xc6;
                           (* VPMULDQ (%_% ymm0) (%_% ymm14) (%_% ymm14) *)
  0xc4; 0x41; 0x7e; 0x16; 0xd2;
                           (* VMOVSHDUP (%_% ymm10) (%_% ymm10) *)
  0xc4; 0x43; 0x2d; 0x02; 0xe2; 0xaa;
                           (* VPBLENDD (%_% ymm12) (%_% ymm10) (%_% ymm10) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x3d; 0xfa; 0xd4;
                           (* VPSUBD (%_% ymm10) (%_% ymm8) (%_% ymm12) *)
  0xc4; 0x41; 0x3d; 0xfe; 0xd0;
                           (* VPADDD (%_% ymm10) (%_% ymm8) (%_% ymm8) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xf5; 0xaa;
                           (* VPBLENDD (%_% ymm14) (%_% ymm13) (%_% ymm13) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x1d; 0xfe; 0xea;
                           (* VPADDD (%_% ymm13) (%_% ymm12) (%_% ymm10) *)
  0xc4; 0x41; 0x3d; 0xfa; 0xe8;
                           (* VPSUBD (%_% ymm13) (%_% ymm8) (%_% ymm8) *)
  0xc4; 0xc2; 0x4d; 0x28; 0xcd;
                           (* VPMULDQ (%_% ymm1) (%_% ymm6) (%_% ymm13) *)
  0xc4; 0xc1; 0x7e; 0x16; 0xf4;
                           (* VMOVSHDUP (%_% ymm6) (%_% ymm12) *)
  0xc4; 0xc2; 0x1d; 0x28; 0xce;
                           (* VPMULDQ (%_% ymm1) (%_% ymm12) (%_% ymm14) *)
  0xc4; 0xe2; 0x4d; 0x28; 0xd6;
                           (* VPMULDQ (%_% ymm2) (%_% ymm6) (%_% ymm6) *)
  0xc4; 0xc2; 0x1d; 0x28; 0xd4;
                           (* VPMULDQ (%_% ymm2) (%_% ymm12) (%_% ymm12) *)
  0xc4; 0xc2; 0x15; 0x28; 0xc5;
                           (* VPMULDQ (%_% ymm0) (%_% ymm13) (%_% ymm13) *)
  0xc4; 0xc2; 0x0d; 0x28; 0xc6;
                           (* VPMULDQ (%_% ymm0) (%_% ymm14) (%_% ymm14) *)
  0xc5; 0xfe; 0x16; 0xf6;  (* VMOVSHDUP (%_% ymm6) (%_% ymm6) *)
  0xc4; 0x63; 0x4d; 0x02; 0xe6; 0xaa;
                           (* VPBLENDD (%_% ymm12) (%_% ymm6) (%_% ymm6) (Imm8 (word 170)) *)
  0xc4; 0xc1; 0x5d; 0xfa; 0xf4;
                           (* VPSUBD (%_% ymm6) (%_% ymm4) (%_% ymm12) *)
  0xc5; 0xdd; 0xfe; 0xf4;  (* VPADDD (%_% ymm6) (%_% ymm4) (%_% ymm4) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xf5; 0xaa;
                           (* VPBLENDD (%_% ymm14) (%_% ymm13) (%_% ymm13) (Imm8 (word 170)) *)
  0xc5; 0x1d; 0xfe; 0xee;  (* VPADDD (%_% ymm13) (%_% ymm12) (%_% ymm6) *)
  0xc5; 0x5d; 0xfa; 0xec;  (* VPSUBD (%_% ymm13) (%_% ymm4) (%_% ymm4) *)
  0xc4; 0xc2; 0x25; 0x28; 0xcd;
                           (* VPMULDQ (%_% ymm1) (%_% ymm11) (%_% ymm13) *)
  0xc4; 0x41; 0x7e; 0x16; 0xdc;
                           (* VMOVSHDUP (%_% ymm11) (%_% ymm12) *)
  0xc4; 0xc2; 0x1d; 0x28; 0xce;
                           (* VPMULDQ (%_% ymm1) (%_% ymm12) (%_% ymm14) *)
  0xc4; 0xc2; 0x25; 0x28; 0xd3;
                           (* VPMULDQ (%_% ymm2) (%_% ymm11) (%_% ymm11) *)
  0xc4; 0xc2; 0x1d; 0x28; 0xd4;
                           (* VPMULDQ (%_% ymm2) (%_% ymm12) (%_% ymm12) *)
  0xc4; 0xc2; 0x15; 0x28; 0xc5;
                           (* VPMULDQ (%_% ymm0) (%_% ymm13) (%_% ymm13) *)
  0xc4; 0xc2; 0x0d; 0x28; 0xc6;
                           (* VPMULDQ (%_% ymm0) (%_% ymm14) (%_% ymm14) *)
  0xc4; 0x41; 0x7e; 0x16; 0xdb;
                           (* VMOVSHDUP (%_% ymm11) (%_% ymm11) *)
  0xc4; 0x43; 0x25; 0x02; 0xe3; 0xaa;
                           (* VPBLENDD (%_% ymm12) (%_% ymm11) (%_% ymm11) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x35; 0xfa; 0xdc;
                           (* VPSUBD (%_% ymm11) (%_% ymm9) (%_% ymm12) *)
  0xc4; 0x41; 0x35; 0xfe; 0xd9;
                           (* VPADDD (%_% ymm11) (%_% ymm9) (%_% ymm9) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xf5; 0xaa;
                           (* VPBLENDD (%_% ymm14) (%_% ymm13) (%_% ymm13) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x1d; 0xfe; 0xeb;
                           (* VPADDD (%_% ymm13) (%_% ymm12) (%_% ymm11) *)
  0xc4; 0x41; 0x35; 0xfa; 0xe9;
                           (* VPSUBD (%_% ymm13) (%_% ymm9) (%_% ymm9) *)
  0xc5; 0xe5; 0x6c; 0xfd;  (* VPUNPCKLQDQ (%_% ymm7) (%_% ymm3) (%_% ymm5) *)
  0xc5; 0xe5; 0x6d; 0xed;  (* VPUNPCKHQDQ (%_% ymm5) (%_% ymm3) (%_% ymm5) *)
  0xc4; 0xc1; 0x3d; 0x6c; 0xda;
                           (* VPUNPCKLQDQ (%_% ymm3) (%_% ymm8) (%_% ymm10) *)
  0xc4; 0x41; 0x3d; 0x6d; 0xd2;
                           (* VPUNPCKHQDQ (%_% ymm10) (%_% ymm8) (%_% ymm10) *)
  0xc5; 0x5d; 0x6c; 0xc6;  (* VPUNPCKLQDQ (%_% ymm8) (%_% ymm4) (%_% ymm6) *)
  0xc5; 0xdd; 0x6d; 0xf6;  (* VPUNPCKHQDQ (%_% ymm6) (%_% ymm4) (%_% ymm6) *)
  0xc4; 0xc1; 0x35; 0x6c; 0xe3;
                           (* VPUNPCKLQDQ (%_% ymm4) (%_% ymm9) (%_% ymm11) *)
  0xc4; 0x41; 0x35; 0x6d; 0xdb;
                           (* VPUNPCKHQDQ (%_% ymm11) (%_% ymm9) (%_% ymm11) *)
  0xc5; 0xfd; 0x6f; 0x8e; 0x40; 0x01; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm1) (Memop Word256 (%% (rsi,320))) *)
  0xc5; 0xfd; 0x6f; 0x96; 0xe0; 0x05; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm2) (Memop Word256 (%% (rsi,1504))) *)
  0xc4; 0xc2; 0x3d; 0x28; 0xcd;
                           (* VPMULDQ (%_% ymm1) (%_% ymm8) (%_% ymm13) *)
  0xc4; 0x41; 0x7e; 0x16; 0xc4;
                           (* VMOVSHDUP (%_% ymm8) (%_% ymm12) *)
  0xc4; 0xc2; 0x1d; 0x28; 0xce;
                           (* VPMULDQ (%_% ymm1) (%_% ymm12) (%_% ymm14) *)
  0xc4; 0xc2; 0x3d; 0x28; 0xd0;
                           (* VPMULDQ (%_% ymm2) (%_% ymm8) (%_% ymm8) *)
  0xc4; 0xc2; 0x1d; 0x28; 0xd4;
                           (* VPMULDQ (%_% ymm2) (%_% ymm12) (%_% ymm12) *)
  0xc4; 0xc2; 0x15; 0x28; 0xc5;
                           (* VPMULDQ (%_% ymm0) (%_% ymm13) (%_% ymm13) *)
  0xc4; 0xc2; 0x0d; 0x28; 0xc6;
                           (* VPMULDQ (%_% ymm0) (%_% ymm14) (%_% ymm14) *)
  0xc4; 0x41; 0x7e; 0x16; 0xc0;
                           (* VMOVSHDUP (%_% ymm8) (%_% ymm8) *)
  0xc4; 0x43; 0x3d; 0x02; 0xe0; 0xaa;
                           (* VPBLENDD (%_% ymm12) (%_% ymm8) (%_% ymm8) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x45; 0xfa; 0xc4;
                           (* VPSUBD (%_% ymm8) (%_% ymm7) (%_% ymm12) *)
  0xc5; 0x45; 0xfe; 0xc7;  (* VPADDD (%_% ymm8) (%_% ymm7) (%_% ymm7) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xf5; 0xaa;
                           (* VPBLENDD (%_% ymm14) (%_% ymm13) (%_% ymm13) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x1d; 0xfe; 0xe8;
                           (* VPADDD (%_% ymm13) (%_% ymm12) (%_% ymm8) *)
  0xc5; 0x45; 0xfa; 0xef;  (* VPSUBD (%_% ymm13) (%_% ymm7) (%_% ymm7) *)
  0xc4; 0xc2; 0x4d; 0x28; 0xcd;
                           (* VPMULDQ (%_% ymm1) (%_% ymm6) (%_% ymm13) *)
  0xc4; 0xc1; 0x7e; 0x16; 0xf4;
                           (* VMOVSHDUP (%_% ymm6) (%_% ymm12) *)
  0xc4; 0xc2; 0x1d; 0x28; 0xce;
                           (* VPMULDQ (%_% ymm1) (%_% ymm12) (%_% ymm14) *)
  0xc4; 0xe2; 0x4d; 0x28; 0xd6;
                           (* VPMULDQ (%_% ymm2) (%_% ymm6) (%_% ymm6) *)
  0xc4; 0xc2; 0x1d; 0x28; 0xd4;
                           (* VPMULDQ (%_% ymm2) (%_% ymm12) (%_% ymm12) *)
  0xc4; 0xc2; 0x15; 0x28; 0xc5;
                           (* VPMULDQ (%_% ymm0) (%_% ymm13) (%_% ymm13) *)
  0xc4; 0xc2; 0x0d; 0x28; 0xc6;
                           (* VPMULDQ (%_% ymm0) (%_% ymm14) (%_% ymm14) *)
  0xc5; 0xfe; 0x16; 0xf6;  (* VMOVSHDUP (%_% ymm6) (%_% ymm6) *)
  0xc4; 0x63; 0x4d; 0x02; 0xe6; 0xaa;
                           (* VPBLENDD (%_% ymm12) (%_% ymm6) (%_% ymm6) (Imm8 (word 170)) *)
  0xc4; 0xc1; 0x55; 0xfa; 0xf4;
                           (* VPSUBD (%_% ymm6) (%_% ymm5) (%_% ymm12) *)
  0xc5; 0xd5; 0xfe; 0xf5;  (* VPADDD (%_% ymm6) (%_% ymm5) (%_% ymm5) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xf5; 0xaa;
                           (* VPBLENDD (%_% ymm14) (%_% ymm13) (%_% ymm13) (Imm8 (word 170)) *)
  0xc5; 0x1d; 0xfe; 0xee;  (* VPADDD (%_% ymm13) (%_% ymm12) (%_% ymm6) *)
  0xc5; 0x55; 0xfa; 0xed;  (* VPSUBD (%_% ymm13) (%_% ymm5) (%_% ymm5) *)
  0xc4; 0xc2; 0x5d; 0x28; 0xcd;
                           (* VPMULDQ (%_% ymm1) (%_% ymm4) (%_% ymm13) *)
  0xc4; 0xc1; 0x7e; 0x16; 0xe4;
                           (* VMOVSHDUP (%_% ymm4) (%_% ymm12) *)
  0xc4; 0xc2; 0x1d; 0x28; 0xce;
                           (* VPMULDQ (%_% ymm1) (%_% ymm12) (%_% ymm14) *)
  0xc4; 0xe2; 0x5d; 0x28; 0xd4;
                           (* VPMULDQ (%_% ymm2) (%_% ymm4) (%_% ymm4) *)
  0xc4; 0xc2; 0x1d; 0x28; 0xd4;
                           (* VPMULDQ (%_% ymm2) (%_% ymm12) (%_% ymm12) *)
  0xc4; 0xc2; 0x15; 0x28; 0xc5;
                           (* VPMULDQ (%_% ymm0) (%_% ymm13) (%_% ymm13) *)
  0xc4; 0xc2; 0x0d; 0x28; 0xc6;
                           (* VPMULDQ (%_% ymm0) (%_% ymm14) (%_% ymm14) *)
  0xc5; 0xfe; 0x16; 0xe4;  (* VMOVSHDUP (%_% ymm4) (%_% ymm4) *)
  0xc4; 0x63; 0x5d; 0x02; 0xe4; 0xaa;
                           (* VPBLENDD (%_% ymm12) (%_% ymm4) (%_% ymm4) (Imm8 (word 170)) *)
  0xc4; 0xc1; 0x65; 0xfa; 0xe4;
                           (* VPSUBD (%_% ymm4) (%_% ymm3) (%_% ymm12) *)
  0xc5; 0xe5; 0xfe; 0xe3;  (* VPADDD (%_% ymm4) (%_% ymm3) (%_% ymm3) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xf5; 0xaa;
                           (* VPBLENDD (%_% ymm14) (%_% ymm13) (%_% ymm13) (Imm8 (word 170)) *)
  0xc5; 0x1d; 0xfe; 0xec;  (* VPADDD (%_% ymm13) (%_% ymm12) (%_% ymm4) *)
  0xc5; 0x65; 0xfa; 0xeb;  (* VPSUBD (%_% ymm13) (%_% ymm3) (%_% ymm3) *)
  0xc4; 0xc2; 0x25; 0x28; 0xcd;
                           (* VPMULDQ (%_% ymm1) (%_% ymm11) (%_% ymm13) *)
  0xc4; 0x41; 0x7e; 0x16; 0xdc;
                           (* VMOVSHDUP (%_% ymm11) (%_% ymm12) *)
  0xc4; 0xc2; 0x1d; 0x28; 0xce;
                           (* VPMULDQ (%_% ymm1) (%_% ymm12) (%_% ymm14) *)
  0xc4; 0xc2; 0x25; 0x28; 0xd3;
                           (* VPMULDQ (%_% ymm2) (%_% ymm11) (%_% ymm11) *)
  0xc4; 0xc2; 0x1d; 0x28; 0xd4;
                           (* VPMULDQ (%_% ymm2) (%_% ymm12) (%_% ymm12) *)
  0xc4; 0xc2; 0x15; 0x28; 0xc5;
                           (* VPMULDQ (%_% ymm0) (%_% ymm13) (%_% ymm13) *)
  0xc4; 0xc2; 0x0d; 0x28; 0xc6;
                           (* VPMULDQ (%_% ymm0) (%_% ymm14) (%_% ymm14) *)
  0xc4; 0x41; 0x7e; 0x16; 0xdb;
                           (* VMOVSHDUP (%_% ymm11) (%_% ymm11) *)
  0xc4; 0x43; 0x25; 0x02; 0xe3; 0xaa;
                           (* VPBLENDD (%_% ymm12) (%_% ymm11) (%_% ymm11) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x2d; 0xfa; 0xdc;
                           (* VPSUBD (%_% ymm11) (%_% ymm10) (%_% ymm12) *)
  0xc4; 0x41; 0x2d; 0xfe; 0xda;
                           (* VPADDD (%_% ymm11) (%_% ymm10) (%_% ymm10) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xf5; 0xaa;
                           (* VPBLENDD (%_% ymm14) (%_% ymm13) (%_% ymm13) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x1d; 0xfe; 0xeb;
                           (* VPADDD (%_% ymm13) (%_% ymm12) (%_% ymm11) *)
  0xc4; 0x41; 0x2d; 0xfa; 0xea;
                           (* VPSUBD (%_% ymm13) (%_% ymm10) (%_% ymm10) *)
  0xc4; 0x41; 0x7e; 0x12; 0xc8;
                           (* VMOVSLDUP (%_% ymm9) (%_% ymm8) *)
  0xc4; 0x63; 0x35; 0x02; 0xcf; 0xaa;
                           (* VPBLENDD (%_% ymm9) (%_% ymm9) (%_% ymm7) (Imm8 (word 170)) *)
  0xc5; 0xc5; 0x73; 0xd7; 0x20;
                           (* VPSRLQ (%_% ymm7) (%_% ymm7) (Imm8 (word 32)) *)
  0xc4; 0x63; 0x3d; 0x02; 0xc7; 0xaa;
                           (* VPBLENDD (%_% ymm8) (%_% ymm8) (%_% ymm7) (Imm8 (word 170)) *)
  0xc5; 0xfe; 0x12; 0xfe;  (* VMOVSLDUP (%_% ymm7) (%_% ymm6) *)
  0xc4; 0xe3; 0x45; 0x02; 0xfd; 0xaa;
                           (* VPBLENDD (%_% ymm7) (%_% ymm7) (%_% ymm5) (Imm8 (word 170)) *)
  0xc5; 0xd5; 0x73; 0xd5; 0x20;
                           (* VPSRLQ (%_% ymm5) (%_% ymm5) (Imm8 (word 32)) *)
  0xc4; 0xe3; 0x4d; 0x02; 0xf5; 0xaa;
                           (* VPBLENDD (%_% ymm6) (%_% ymm6) (%_% ymm5) (Imm8 (word 170)) *)
  0xc5; 0xfe; 0x12; 0xec;  (* VMOVSLDUP (%_% ymm5) (%_% ymm4) *)
  0xc4; 0xe3; 0x55; 0x02; 0xeb; 0xaa;
                           (* VPBLENDD (%_% ymm5) (%_% ymm5) (%_% ymm3) (Imm8 (word 170)) *)
  0xc5; 0xe5; 0x73; 0xd3; 0x20;
                           (* VPSRLQ (%_% ymm3) (%_% ymm3) (Imm8 (word 32)) *)
  0xc4; 0xe3; 0x5d; 0x02; 0xe3; 0xaa;
                           (* VPBLENDD (%_% ymm4) (%_% ymm4) (%_% ymm3) (Imm8 (word 170)) *)
  0xc4; 0xc1; 0x7e; 0x12; 0xdb;
                           (* VMOVSLDUP (%_% ymm3) (%_% ymm11) *)
  0xc4; 0xc3; 0x65; 0x02; 0xda; 0xaa;
                           (* VPBLENDD (%_% ymm3) (%_% ymm3) (%_% ymm10) (Imm8 (word 170)) *)
  0xc4; 0xc1; 0x2d; 0x73; 0xd2; 0x20;
                           (* VPSRLQ (%_% ymm10) (%_% ymm10) (Imm8 (word 32)) *)
  0xc4; 0x43; 0x25; 0x02; 0xda; 0xaa;
                           (* VPBLENDD (%_% ymm11) (%_% ymm11) (%_% ymm10) (Imm8 (word 170)) *)
  0xc5; 0xfd; 0x6f; 0x8e; 0xc0; 0x01; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm1) (Memop Word256 (%% (rsi,448))) *)
  0xc5; 0xfd; 0x6f; 0x96; 0x60; 0x06; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm2) (Memop Word256 (%% (rsi,1632))) *)
  0xc4; 0xc1; 0x75; 0x73; 0xd2; 0x20;
                           (* VPSRLQ (%_% ymm1) (%_% ymm10) (Imm8 (word 32)) *)
  0xc4; 0xc1; 0x7e; 0x16; 0xd7;
                           (* VMOVSHDUP (%_% ymm2) (%_% ymm15) *)
  0xc4; 0xc2; 0x55; 0x28; 0xcd;
                           (* VPMULDQ (%_% ymm1) (%_% ymm5) (%_% ymm13) *)
  0xc4; 0xc1; 0x7e; 0x16; 0xec;
                           (* VMOVSHDUP (%_% ymm5) (%_% ymm12) *)
  0xc4; 0x42; 0x1d; 0x28; 0xd6;
                           (* VPMULDQ (%_% ymm10) (%_% ymm12) (%_% ymm14) *)
  0xc4; 0xe2; 0x55; 0x28; 0xd5;
                           (* VPMULDQ (%_% ymm2) (%_% ymm5) (%_% ymm5) *)
  0xc4; 0x42; 0x1d; 0x28; 0xfc;
                           (* VPMULDQ (%_% ymm15) (%_% ymm12) (%_% ymm12) *)
  0xc4; 0xc2; 0x15; 0x28; 0xc5;
                           (* VPMULDQ (%_% ymm0) (%_% ymm13) (%_% ymm13) *)
  0xc4; 0xc2; 0x0d; 0x28; 0xc6;
                           (* VPMULDQ (%_% ymm0) (%_% ymm14) (%_% ymm14) *)
  0xc5; 0xfe; 0x16; 0xed;  (* VMOVSHDUP (%_% ymm5) (%_% ymm5) *)
  0xc4; 0x63; 0x55; 0x02; 0xe5; 0xaa;
                           (* VPBLENDD (%_% ymm12) (%_% ymm5) (%_% ymm5) (Imm8 (word 170)) *)
  0xc4; 0xc1; 0x35; 0xfa; 0xec;
                           (* VPSUBD (%_% ymm5) (%_% ymm9) (%_% ymm12) *)
  0xc4; 0xc1; 0x35; 0xfe; 0xe9;
                           (* VPADDD (%_% ymm5) (%_% ymm9) (%_% ymm9) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xf5; 0xaa;
                           (* VPBLENDD (%_% ymm14) (%_% ymm13) (%_% ymm13) (Imm8 (word 170)) *)
  0xc5; 0x1d; 0xfe; 0xed;  (* VPADDD (%_% ymm13) (%_% ymm12) (%_% ymm5) *)
  0xc4; 0x41; 0x35; 0xfa; 0xe9;
                           (* VPSUBD (%_% ymm13) (%_% ymm9) (%_% ymm9) *)
  0xc4; 0xc2; 0x5d; 0x28; 0xcd;
                           (* VPMULDQ (%_% ymm1) (%_% ymm4) (%_% ymm13) *)
  0xc4; 0xc1; 0x7e; 0x16; 0xe4;
                           (* VMOVSHDUP (%_% ymm4) (%_% ymm12) *)
  0xc4; 0x42; 0x1d; 0x28; 0xd6;
                           (* VPMULDQ (%_% ymm10) (%_% ymm12) (%_% ymm14) *)
  0xc4; 0xe2; 0x5d; 0x28; 0xd4;
                           (* VPMULDQ (%_% ymm2) (%_% ymm4) (%_% ymm4) *)
  0xc4; 0x42; 0x1d; 0x28; 0xfc;
                           (* VPMULDQ (%_% ymm15) (%_% ymm12) (%_% ymm12) *)
  0xc4; 0xc2; 0x15; 0x28; 0xc5;
                           (* VPMULDQ (%_% ymm0) (%_% ymm13) (%_% ymm13) *)
  0xc4; 0xc2; 0x0d; 0x28; 0xc6;
                           (* VPMULDQ (%_% ymm0) (%_% ymm14) (%_% ymm14) *)
  0xc5; 0xfe; 0x16; 0xe4;  (* VMOVSHDUP (%_% ymm4) (%_% ymm4) *)
  0xc4; 0x63; 0x5d; 0x02; 0xe4; 0xaa;
                           (* VPBLENDD (%_% ymm12) (%_% ymm4) (%_% ymm4) (Imm8 (word 170)) *)
  0xc4; 0xc1; 0x3d; 0xfa; 0xe4;
                           (* VPSUBD (%_% ymm4) (%_% ymm8) (%_% ymm12) *)
  0xc4; 0xc1; 0x3d; 0xfe; 0xe0;
                           (* VPADDD (%_% ymm4) (%_% ymm8) (%_% ymm8) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xf5; 0xaa;
                           (* VPBLENDD (%_% ymm14) (%_% ymm13) (%_% ymm13) (Imm8 (word 170)) *)
  0xc5; 0x1d; 0xfe; 0xec;  (* VPADDD (%_% ymm13) (%_% ymm12) (%_% ymm4) *)
  0xc4; 0x41; 0x3d; 0xfa; 0xe8;
                           (* VPSUBD (%_% ymm13) (%_% ymm8) (%_% ymm8) *)
  0xc4; 0xc2; 0x65; 0x28; 0xcd;
                           (* VPMULDQ (%_% ymm1) (%_% ymm3) (%_% ymm13) *)
  0xc4; 0xc1; 0x7e; 0x16; 0xdc;
                           (* VMOVSHDUP (%_% ymm3) (%_% ymm12) *)
  0xc4; 0x42; 0x1d; 0x28; 0xd6;
                           (* VPMULDQ (%_% ymm10) (%_% ymm12) (%_% ymm14) *)
  0xc4; 0xe2; 0x65; 0x28; 0xd3;
                           (* VPMULDQ (%_% ymm2) (%_% ymm3) (%_% ymm3) *)
  0xc4; 0x42; 0x1d; 0x28; 0xfc;
                           (* VPMULDQ (%_% ymm15) (%_% ymm12) (%_% ymm12) *)
  0xc4; 0xc2; 0x15; 0x28; 0xc5;
                           (* VPMULDQ (%_% ymm0) (%_% ymm13) (%_% ymm13) *)
  0xc4; 0xc2; 0x0d; 0x28; 0xc6;
                           (* VPMULDQ (%_% ymm0) (%_% ymm14) (%_% ymm14) *)
  0xc5; 0xfe; 0x16; 0xdb;  (* VMOVSHDUP (%_% ymm3) (%_% ymm3) *)
  0xc4; 0x63; 0x65; 0x02; 0xe3; 0xaa;
                           (* VPBLENDD (%_% ymm12) (%_% ymm3) (%_% ymm3) (Imm8 (word 170)) *)
  0xc4; 0xc1; 0x45; 0xfa; 0xdc;
                           (* VPSUBD (%_% ymm3) (%_% ymm7) (%_% ymm12) *)
  0xc5; 0xc5; 0xfe; 0xdf;  (* VPADDD (%_% ymm3) (%_% ymm7) (%_% ymm7) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xf5; 0xaa;
                           (* VPBLENDD (%_% ymm14) (%_% ymm13) (%_% ymm13) (Imm8 (word 170)) *)
  0xc5; 0x1d; 0xfe; 0xeb;  (* VPADDD (%_% ymm13) (%_% ymm12) (%_% ymm3) *)
  0xc5; 0x45; 0xfa; 0xef;  (* VPSUBD (%_% ymm13) (%_% ymm7) (%_% ymm7) *)
  0xc4; 0xc2; 0x25; 0x28; 0xcd;
                           (* VPMULDQ (%_% ymm1) (%_% ymm11) (%_% ymm13) *)
  0xc4; 0x41; 0x7e; 0x16; 0xdc;
                           (* VMOVSHDUP (%_% ymm11) (%_% ymm12) *)
  0xc4; 0x42; 0x1d; 0x28; 0xd6;
                           (* VPMULDQ (%_% ymm10) (%_% ymm12) (%_% ymm14) *)
  0xc4; 0xc2; 0x25; 0x28; 0xd3;
                           (* VPMULDQ (%_% ymm2) (%_% ymm11) (%_% ymm11) *)
  0xc4; 0x42; 0x1d; 0x28; 0xfc;
                           (* VPMULDQ (%_% ymm15) (%_% ymm12) (%_% ymm12) *)
  0xc4; 0xc2; 0x15; 0x28; 0xc5;
                           (* VPMULDQ (%_% ymm0) (%_% ymm13) (%_% ymm13) *)
  0xc4; 0xc2; 0x0d; 0x28; 0xc6;
                           (* VPMULDQ (%_% ymm0) (%_% ymm14) (%_% ymm14) *)
  0xc4; 0x41; 0x7e; 0x16; 0xdb;
                           (* VMOVSHDUP (%_% ymm11) (%_% ymm11) *)
  0xc4; 0x43; 0x25; 0x02; 0xe3; 0xaa;
                           (* VPBLENDD (%_% ymm12) (%_% ymm11) (%_% ymm11) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x4d; 0xfa; 0xdc;
                           (* VPSUBD (%_% ymm11) (%_% ymm6) (%_% ymm12) *)
  0xc5; 0x4d; 0xfe; 0xde;  (* VPADDD (%_% ymm11) (%_% ymm6) (%_% ymm6) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xf5; 0xaa;
                           (* VPBLENDD (%_% ymm14) (%_% ymm13) (%_% ymm13) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x1d; 0xfe; 0xeb;
                           (* VPADDD (%_% ymm13) (%_% ymm12) (%_% ymm11) *)
  0xc5; 0x4d; 0xfa; 0xee;  (* VPSUBD (%_% ymm13) (%_% ymm6) (%_% ymm6) *)
  0xc5; 0xfd; 0x6f; 0x8e; 0x40; 0x02; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm1) (Memop Word256 (%% (rsi,576))) *)
  0xc5; 0xfd; 0x6f; 0x96; 0xe0; 0x06; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm2) (Memop Word256 (%% (rsi,1760))) *)
  0xc4; 0xc1; 0x75; 0x73; 0xd2; 0x20;
                           (* VPSRLQ (%_% ymm1) (%_% ymm10) (Imm8 (word 32)) *)
  0xc4; 0xc1; 0x7e; 0x16; 0xd7;
                           (* VMOVSHDUP (%_% ymm2) (%_% ymm15) *)
  0xc4; 0xc2; 0x45; 0x28; 0xcd;
                           (* VPMULDQ (%_% ymm1) (%_% ymm7) (%_% ymm13) *)
  0xc4; 0xc1; 0x7e; 0x16; 0xfc;
                           (* VMOVSHDUP (%_% ymm7) (%_% ymm12) *)
  0xc4; 0x42; 0x1d; 0x28; 0xd6;
                           (* VPMULDQ (%_% ymm10) (%_% ymm12) (%_% ymm14) *)
  0xc4; 0xe2; 0x45; 0x28; 0xd7;
                           (* VPMULDQ (%_% ymm2) (%_% ymm7) (%_% ymm7) *)
  0xc4; 0x42; 0x1d; 0x28; 0xfc;
                           (* VPMULDQ (%_% ymm15) (%_% ymm12) (%_% ymm12) *)
  0xc4; 0xc2; 0x15; 0x28; 0xc5;
                           (* VPMULDQ (%_% ymm0) (%_% ymm13) (%_% ymm13) *)
  0xc4; 0xc2; 0x0d; 0x28; 0xc6;
                           (* VPMULDQ (%_% ymm0) (%_% ymm14) (%_% ymm14) *)
  0xc5; 0xfe; 0x16; 0xff;  (* VMOVSHDUP (%_% ymm7) (%_% ymm7) *)
  0xc4; 0x63; 0x45; 0x02; 0xe7; 0xaa;
                           (* VPBLENDD (%_% ymm12) (%_% ymm7) (%_% ymm7) (Imm8 (word 170)) *)
  0xc4; 0xc1; 0x35; 0xfa; 0xfc;
                           (* VPSUBD (%_% ymm7) (%_% ymm9) (%_% ymm12) *)
  0xc4; 0xc1; 0x35; 0xfe; 0xf9;
                           (* VPADDD (%_% ymm7) (%_% ymm9) (%_% ymm9) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xf5; 0xaa;
                           (* VPBLENDD (%_% ymm14) (%_% ymm13) (%_% ymm13) (Imm8 (word 170)) *)
  0xc5; 0x1d; 0xfe; 0xef;  (* VPADDD (%_% ymm13) (%_% ymm12) (%_% ymm7) *)
  0xc4; 0x41; 0x35; 0xfa; 0xe9;
                           (* VPSUBD (%_% ymm13) (%_% ymm9) (%_% ymm9) *)
  0xc4; 0xc2; 0x4d; 0x28; 0xcd;
                           (* VPMULDQ (%_% ymm1) (%_% ymm6) (%_% ymm13) *)
  0xc4; 0xc1; 0x7e; 0x16; 0xf4;
                           (* VMOVSHDUP (%_% ymm6) (%_% ymm12) *)
  0xc4; 0x42; 0x1d; 0x28; 0xd6;
                           (* VPMULDQ (%_% ymm10) (%_% ymm12) (%_% ymm14) *)
  0xc4; 0xe2; 0x4d; 0x28; 0xd6;
                           (* VPMULDQ (%_% ymm2) (%_% ymm6) (%_% ymm6) *)
  0xc4; 0x42; 0x1d; 0x28; 0xfc;
                           (* VPMULDQ (%_% ymm15) (%_% ymm12) (%_% ymm12) *)
  0xc4; 0xc2; 0x15; 0x28; 0xc5;
                           (* VPMULDQ (%_% ymm0) (%_% ymm13) (%_% ymm13) *)
  0xc4; 0xc2; 0x0d; 0x28; 0xc6;
                           (* VPMULDQ (%_% ymm0) (%_% ymm14) (%_% ymm14) *)
  0xc5; 0xfe; 0x16; 0xf6;  (* VMOVSHDUP (%_% ymm6) (%_% ymm6) *)
  0xc4; 0x63; 0x4d; 0x02; 0xe6; 0xaa;
                           (* VPBLENDD (%_% ymm12) (%_% ymm6) (%_% ymm6) (Imm8 (word 170)) *)
  0xc4; 0xc1; 0x3d; 0xfa; 0xf4;
                           (* VPSUBD (%_% ymm6) (%_% ymm8) (%_% ymm12) *)
  0xc4; 0xc1; 0x3d; 0xfe; 0xf0;
                           (* VPADDD (%_% ymm6) (%_% ymm8) (%_% ymm8) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xf5; 0xaa;
                           (* VPBLENDD (%_% ymm14) (%_% ymm13) (%_% ymm13) (Imm8 (word 170)) *)
  0xc5; 0x1d; 0xfe; 0xee;  (* VPADDD (%_% ymm13) (%_% ymm12) (%_% ymm6) *)
  0xc4; 0x41; 0x3d; 0xfa; 0xe8;
                           (* VPSUBD (%_% ymm13) (%_% ymm8) (%_% ymm8) *)
  0xc5; 0xfd; 0x6f; 0x8e; 0xc0; 0x02; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm1) (Memop Word256 (%% (rsi,704))) *)
  0xc5; 0xfd; 0x6f; 0x96; 0x60; 0x07; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm2) (Memop Word256 (%% (rsi,1888))) *)
  0xc4; 0xc1; 0x75; 0x73; 0xd2; 0x20;
                           (* VPSRLQ (%_% ymm1) (%_% ymm10) (Imm8 (word 32)) *)
  0xc4; 0xc1; 0x7e; 0x16; 0xd7;
                           (* VMOVSHDUP (%_% ymm2) (%_% ymm15) *)
  0xc4; 0xc2; 0x65; 0x28; 0xcd;
                           (* VPMULDQ (%_% ymm1) (%_% ymm3) (%_% ymm13) *)
  0xc4; 0xc1; 0x7e; 0x16; 0xdc;
                           (* VMOVSHDUP (%_% ymm3) (%_% ymm12) *)
  0xc4; 0x42; 0x1d; 0x28; 0xd6;
                           (* VPMULDQ (%_% ymm10) (%_% ymm12) (%_% ymm14) *)
  0xc4; 0xe2; 0x65; 0x28; 0xd3;
                           (* VPMULDQ (%_% ymm2) (%_% ymm3) (%_% ymm3) *)
  0xc4; 0x42; 0x1d; 0x28; 0xfc;
                           (* VPMULDQ (%_% ymm15) (%_% ymm12) (%_% ymm12) *)
  0xc4; 0xc2; 0x15; 0x28; 0xc5;
                           (* VPMULDQ (%_% ymm0) (%_% ymm13) (%_% ymm13) *)
  0xc4; 0xc2; 0x0d; 0x28; 0xc6;
                           (* VPMULDQ (%_% ymm0) (%_% ymm14) (%_% ymm14) *)
  0xc5; 0xfe; 0x16; 0xdb;  (* VMOVSHDUP (%_% ymm3) (%_% ymm3) *)
  0xc4; 0x63; 0x65; 0x02; 0xe3; 0xaa;
                           (* VPBLENDD (%_% ymm12) (%_% ymm3) (%_% ymm3) (Imm8 (word 170)) *)
  0xc4; 0xc1; 0x55; 0xfa; 0xdc;
                           (* VPSUBD (%_% ymm3) (%_% ymm5) (%_% ymm12) *)
  0xc5; 0xd5; 0xfe; 0xdd;  (* VPADDD (%_% ymm3) (%_% ymm5) (%_% ymm5) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xf5; 0xaa;
                           (* VPBLENDD (%_% ymm14) (%_% ymm13) (%_% ymm13) (Imm8 (word 170)) *)
  0xc5; 0x1d; 0xfe; 0xeb;  (* VPADDD (%_% ymm13) (%_% ymm12) (%_% ymm3) *)
  0xc5; 0x55; 0xfa; 0xed;  (* VPSUBD (%_% ymm13) (%_% ymm5) (%_% ymm5) *)
  0xc4; 0xc2; 0x25; 0x28; 0xcd;
                           (* VPMULDQ (%_% ymm1) (%_% ymm11) (%_% ymm13) *)
  0xc4; 0x41; 0x7e; 0x16; 0xdc;
                           (* VMOVSHDUP (%_% ymm11) (%_% ymm12) *)
  0xc4; 0x42; 0x1d; 0x28; 0xd6;
                           (* VPMULDQ (%_% ymm10) (%_% ymm12) (%_% ymm14) *)
  0xc4; 0xc2; 0x25; 0x28; 0xd3;
                           (* VPMULDQ (%_% ymm2) (%_% ymm11) (%_% ymm11) *)
  0xc4; 0x42; 0x1d; 0x28; 0xfc;
                           (* VPMULDQ (%_% ymm15) (%_% ymm12) (%_% ymm12) *)
  0xc4; 0xc2; 0x15; 0x28; 0xc5;
                           (* VPMULDQ (%_% ymm0) (%_% ymm13) (%_% ymm13) *)
  0xc4; 0xc2; 0x0d; 0x28; 0xc6;
                           (* VPMULDQ (%_% ymm0) (%_% ymm14) (%_% ymm14) *)
  0xc4; 0x41; 0x7e; 0x16; 0xdb;
                           (* VMOVSHDUP (%_% ymm11) (%_% ymm11) *)
  0xc4; 0x43; 0x25; 0x02; 0xe3; 0xaa;
                           (* VPBLENDD (%_% ymm12) (%_% ymm11) (%_% ymm11) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x5d; 0xfa; 0xdc;
                           (* VPSUBD (%_% ymm11) (%_% ymm4) (%_% ymm12) *)
  0xc5; 0x5d; 0xfe; 0xdc;  (* VPADDD (%_% ymm11) (%_% ymm4) (%_% ymm4) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xf5; 0xaa;
                           (* VPBLENDD (%_% ymm14) (%_% ymm13) (%_% ymm13) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x1d; 0xfe; 0xeb;
                           (* VPADDD (%_% ymm13) (%_% ymm12) (%_% ymm11) *)
  0xc5; 0x5d; 0xfa; 0xec;  (* VPSUBD (%_% ymm13) (%_% ymm4) (%_% ymm4) *)
  0xc5; 0xfd; 0x6f; 0x8e; 0x40; 0x03; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm1) (Memop Word256 (%% (rsi,832))) *)
  0xc5; 0xfd; 0x6f; 0x96; 0xe0; 0x07; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm2) (Memop Word256 (%% (rsi,2016))) *)
  0xc4; 0xc1; 0x75; 0x73; 0xd2; 0x20;
                           (* VPSRLQ (%_% ymm1) (%_% ymm10) (Imm8 (word 32)) *)
  0xc4; 0xc1; 0x7e; 0x16; 0xd7;
                           (* VMOVSHDUP (%_% ymm2) (%_% ymm15) *)
  0xc4; 0xc2; 0x3d; 0x28; 0xcd;
                           (* VPMULDQ (%_% ymm1) (%_% ymm8) (%_% ymm13) *)
  0xc4; 0x41; 0x7e; 0x16; 0xc4;
                           (* VMOVSHDUP (%_% ymm8) (%_% ymm12) *)
  0xc4; 0x42; 0x1d; 0x28; 0xd6;
                           (* VPMULDQ (%_% ymm10) (%_% ymm12) (%_% ymm14) *)
  0xc4; 0xc2; 0x3d; 0x28; 0xd0;
                           (* VPMULDQ (%_% ymm2) (%_% ymm8) (%_% ymm8) *)
  0xc4; 0x42; 0x1d; 0x28; 0xfc;
                           (* VPMULDQ (%_% ymm15) (%_% ymm12) (%_% ymm12) *)
  0xc4; 0xc2; 0x15; 0x28; 0xc5;
                           (* VPMULDQ (%_% ymm0) (%_% ymm13) (%_% ymm13) *)
  0xc4; 0xc2; 0x0d; 0x28; 0xc6;
                           (* VPMULDQ (%_% ymm0) (%_% ymm14) (%_% ymm14) *)
  0xc4; 0x41; 0x7e; 0x16; 0xc0;
                           (* VMOVSHDUP (%_% ymm8) (%_% ymm8) *)
  0xc4; 0x43; 0x3d; 0x02; 0xe0; 0xaa;
                           (* VPBLENDD (%_% ymm12) (%_% ymm8) (%_% ymm8) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x35; 0xfa; 0xc4;
                           (* VPSUBD (%_% ymm8) (%_% ymm9) (%_% ymm12) *)
  0xc4; 0x41; 0x35; 0xfe; 0xc1;
                           (* VPADDD (%_% ymm8) (%_% ymm9) (%_% ymm9) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xf5; 0xaa;
                           (* VPBLENDD (%_% ymm14) (%_% ymm13) (%_% ymm13) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x1d; 0xfe; 0xe8;
                           (* VPADDD (%_% ymm13) (%_% ymm12) (%_% ymm8) *)
  0xc4; 0x41; 0x35; 0xfa; 0xe9;
                           (* VPSUBD (%_% ymm13) (%_% ymm9) (%_% ymm9) *)
  0xc5; 0xfd; 0x6f; 0x8e; 0xc0; 0x03; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm1) (Memop Word256 (%% (rsi,960))) *)
  0xc5; 0xfd; 0x6f; 0x96; 0x60; 0x08; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm2) (Memop Word256 (%% (rsi,2144))) *)
  0xc4; 0xc1; 0x75; 0x73; 0xd2; 0x20;
                           (* VPSRLQ (%_% ymm1) (%_% ymm10) (Imm8 (word 32)) *)
  0xc4; 0xc1; 0x7e; 0x16; 0xd7;
                           (* VMOVSHDUP (%_% ymm2) (%_% ymm15) *)
  0xc4; 0xc2; 0x4d; 0x28; 0xcd;
                           (* VPMULDQ (%_% ymm1) (%_% ymm6) (%_% ymm13) *)
  0xc4; 0xc1; 0x7e; 0x16; 0xf4;
                           (* VMOVSHDUP (%_% ymm6) (%_% ymm12) *)
  0xc4; 0x42; 0x1d; 0x28; 0xd6;
                           (* VPMULDQ (%_% ymm10) (%_% ymm12) (%_% ymm14) *)
  0xc4; 0xe2; 0x4d; 0x28; 0xd6;
                           (* VPMULDQ (%_% ymm2) (%_% ymm6) (%_% ymm6) *)
  0xc4; 0x42; 0x1d; 0x28; 0xfc;
                           (* VPMULDQ (%_% ymm15) (%_% ymm12) (%_% ymm12) *)
  0xc4; 0xc2; 0x15; 0x28; 0xc5;
                           (* VPMULDQ (%_% ymm0) (%_% ymm13) (%_% ymm13) *)
  0xc4; 0xc2; 0x0d; 0x28; 0xc6;
                           (* VPMULDQ (%_% ymm0) (%_% ymm14) (%_% ymm14) *)
  0xc5; 0xfe; 0x16; 0xf6;  (* VMOVSHDUP (%_% ymm6) (%_% ymm6) *)
  0xc4; 0x63; 0x4d; 0x02; 0xe6; 0xaa;
                           (* VPBLENDD (%_% ymm12) (%_% ymm6) (%_% ymm6) (Imm8 (word 170)) *)
  0xc4; 0xc1; 0x45; 0xfa; 0xf4;
                           (* VPSUBD (%_% ymm6) (%_% ymm7) (%_% ymm12) *)
  0xc5; 0xc5; 0xfe; 0xf7;  (* VPADDD (%_% ymm6) (%_% ymm7) (%_% ymm7) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xf5; 0xaa;
                           (* VPBLENDD (%_% ymm14) (%_% ymm13) (%_% ymm13) (Imm8 (word 170)) *)
  0xc5; 0x1d; 0xfe; 0xee;  (* VPADDD (%_% ymm13) (%_% ymm12) (%_% ymm6) *)
  0xc5; 0x45; 0xfa; 0xef;  (* VPSUBD (%_% ymm13) (%_% ymm7) (%_% ymm7) *)
  0xc5; 0xfd; 0x6f; 0x8e; 0x40; 0x04; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm1) (Memop Word256 (%% (rsi,1088))) *)
  0xc5; 0xfd; 0x6f; 0x96; 0xe0; 0x08; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm2) (Memop Word256 (%% (rsi,2272))) *)
  0xc4; 0xc1; 0x75; 0x73; 0xd2; 0x20;
                           (* VPSRLQ (%_% ymm1) (%_% ymm10) (Imm8 (word 32)) *)
  0xc4; 0xc1; 0x7e; 0x16; 0xd7;
                           (* VMOVSHDUP (%_% ymm2) (%_% ymm15) *)
  0xc4; 0xc2; 0x5d; 0x28; 0xcd;
                           (* VPMULDQ (%_% ymm1) (%_% ymm4) (%_% ymm13) *)
  0xc4; 0xc1; 0x7e; 0x16; 0xe4;
                           (* VMOVSHDUP (%_% ymm4) (%_% ymm12) *)
  0xc4; 0x42; 0x1d; 0x28; 0xd6;
                           (* VPMULDQ (%_% ymm10) (%_% ymm12) (%_% ymm14) *)
  0xc4; 0xe2; 0x5d; 0x28; 0xd4;
                           (* VPMULDQ (%_% ymm2) (%_% ymm4) (%_% ymm4) *)
  0xc4; 0x42; 0x1d; 0x28; 0xfc;
                           (* VPMULDQ (%_% ymm15) (%_% ymm12) (%_% ymm12) *)
  0xc4; 0xc2; 0x15; 0x28; 0xc5;
                           (* VPMULDQ (%_% ymm0) (%_% ymm13) (%_% ymm13) *)
  0xc4; 0xc2; 0x0d; 0x28; 0xc6;
                           (* VPMULDQ (%_% ymm0) (%_% ymm14) (%_% ymm14) *)
  0xc5; 0xfe; 0x16; 0xe4;  (* VMOVSHDUP (%_% ymm4) (%_% ymm4) *)
  0xc4; 0x63; 0x5d; 0x02; 0xe4; 0xaa;
                           (* VPBLENDD (%_% ymm12) (%_% ymm4) (%_% ymm4) (Imm8 (word 170)) *)
  0xc4; 0xc1; 0x55; 0xfa; 0xe4;
                           (* VPSUBD (%_% ymm4) (%_% ymm5) (%_% ymm12) *)
  0xc5; 0xd5; 0xfe; 0xe5;  (* VPADDD (%_% ymm4) (%_% ymm5) (%_% ymm5) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xf5; 0xaa;
                           (* VPBLENDD (%_% ymm14) (%_% ymm13) (%_% ymm13) (Imm8 (word 170)) *)
  0xc5; 0x1d; 0xfe; 0xec;  (* VPADDD (%_% ymm13) (%_% ymm12) (%_% ymm4) *)
  0xc5; 0x55; 0xfa; 0xed;  (* VPSUBD (%_% ymm13) (%_% ymm5) (%_% ymm5) *)
  0xc5; 0xfd; 0x6f; 0x8e; 0xc0; 0x04; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm1) (Memop Word256 (%% (rsi,1216))) *)
  0xc5; 0xfd; 0x6f; 0x96; 0x60; 0x09; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm2) (Memop Word256 (%% (rsi,2400))) *)
  0xc4; 0xc1; 0x75; 0x73; 0xd2; 0x20;
                           (* VPSRLQ (%_% ymm1) (%_% ymm10) (Imm8 (word 32)) *)
  0xc4; 0xc1; 0x7e; 0x16; 0xd7;
                           (* VMOVSHDUP (%_% ymm2) (%_% ymm15) *)
  0xc4; 0xc2; 0x25; 0x28; 0xcd;
                           (* VPMULDQ (%_% ymm1) (%_% ymm11) (%_% ymm13) *)
  0xc4; 0x41; 0x7e; 0x16; 0xdc;
                           (* VMOVSHDUP (%_% ymm11) (%_% ymm12) *)
  0xc4; 0x42; 0x1d; 0x28; 0xd6;
                           (* VPMULDQ (%_% ymm10) (%_% ymm12) (%_% ymm14) *)
  0xc4; 0xc2; 0x25; 0x28; 0xd3;
                           (* VPMULDQ (%_% ymm2) (%_% ymm11) (%_% ymm11) *)
  0xc4; 0x42; 0x1d; 0x28; 0xfc;
                           (* VPMULDQ (%_% ymm15) (%_% ymm12) (%_% ymm12) *)
  0xc4; 0xc2; 0x15; 0x28; 0xc5;
                           (* VPMULDQ (%_% ymm0) (%_% ymm13) (%_% ymm13) *)
  0xc4; 0xc2; 0x0d; 0x28; 0xc6;
                           (* VPMULDQ (%_% ymm0) (%_% ymm14) (%_% ymm14) *)
  0xc4; 0x41; 0x7e; 0x16; 0xdb;
                           (* VMOVSHDUP (%_% ymm11) (%_% ymm11) *)
  0xc4; 0x43; 0x25; 0x02; 0xe3; 0xaa;
                           (* VPBLENDD (%_% ymm12) (%_% ymm11) (%_% ymm11) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x65; 0xfa; 0xdc;
                           (* VPSUBD (%_% ymm11) (%_% ymm3) (%_% ymm12) *)
  0xc5; 0x65; 0xfe; 0xdb;  (* VPADDD (%_% ymm11) (%_% ymm3) (%_% ymm3) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xf5; 0xaa;
                           (* VPBLENDD (%_% ymm14) (%_% ymm13) (%_% ymm13) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x1d; 0xfe; 0xeb;
                           (* VPADDD (%_% ymm13) (%_% ymm12) (%_% ymm11) *)
  0xc5; 0x65; 0xfa; 0xeb;  (* VPSUBD (%_% ymm13) (%_% ymm3) (%_% ymm3) *)
  0xc5; 0x7d; 0x7f; 0x8f; 0x00; 0x01; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,256))) (%_% ymm9) *)
  0xc5; 0x7d; 0x7f; 0x87; 0x20; 0x01; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,288))) (%_% ymm8) *)
  0xc5; 0xfd; 0x7f; 0xbf; 0x40; 0x01; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,320))) (%_% ymm7) *)
  0xc5; 0xfd; 0x7f; 0xb7; 0x60; 0x01; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,352))) (%_% ymm6) *)
  0xc5; 0xfd; 0x7f; 0xaf; 0x80; 0x01; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,384))) (%_% ymm5) *)
  0xc5; 0xfd; 0x7f; 0xa7; 0xa0; 0x01; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,416))) (%_% ymm4) *)
  0xc5; 0xfd; 0x7f; 0x9f; 0xc0; 0x01; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,448))) (%_% ymm3) *)
  0xc5; 0x7d; 0x7f; 0x9f; 0xe0; 0x01; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,480))) (%_% ymm11) *)
  0xc5; 0xfd; 0x6f; 0xa7; 0x00; 0x02; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm4) (Memop Word256 (%% (rdi,512))) *)
  0xc5; 0xfd; 0x6f; 0xaf; 0x20; 0x02; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm5) (Memop Word256 (%% (rdi,544))) *)
  0xc5; 0xfd; 0x6f; 0xb7; 0x40; 0x02; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm6) (Memop Word256 (%% (rdi,576))) *)
  0xc5; 0xfd; 0x6f; 0xbf; 0x60; 0x02; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm7) (Memop Word256 (%% (rdi,608))) *)
  0xc5; 0x7d; 0x6f; 0x87; 0x80; 0x02; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm8) (Memop Word256 (%% (rdi,640))) *)
  0xc5; 0x7d; 0x6f; 0x8f; 0xa0; 0x02; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm9) (Memop Word256 (%% (rdi,672))) *)
  0xc5; 0x7d; 0x6f; 0x97; 0xc0; 0x02; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm10) (Memop Word256 (%% (rdi,704))) *)
  0xc5; 0x7d; 0x6f; 0x9f; 0xe0; 0x02; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm11) (Memop Word256 (%% (rdi,736))) *)
  0xc4; 0xe2; 0x7d; 0x58; 0x8e; 0x98; 0x00; 0x00; 0x00;
                           (* VPBROADCASTD (%_% ymm1) (Memop Word128 (%% (rsi,152))) *)
  0xc4; 0xe2; 0x7d; 0x58; 0x96; 0x38; 0x05; 0x00; 0x00;
                           (* VPBROADCASTD (%_% ymm2) (Memop Word128 (%% (rsi,1336))) *)
  0xc4; 0xc2; 0x3d; 0x28; 0xcd;
                           (* VPMULDQ (%_% ymm1) (%_% ymm8) (%_% ymm13) *)
  0xc4; 0x41; 0x7e; 0x16; 0xc4;
                           (* VMOVSHDUP (%_% ymm8) (%_% ymm12) *)
  0xc4; 0xc2; 0x1d; 0x28; 0xce;
                           (* VPMULDQ (%_% ymm1) (%_% ymm12) (%_% ymm14) *)
  0xc4; 0xc2; 0x3d; 0x28; 0xd0;
                           (* VPMULDQ (%_% ymm2) (%_% ymm8) (%_% ymm8) *)
  0xc4; 0xc2; 0x1d; 0x28; 0xd4;
                           (* VPMULDQ (%_% ymm2) (%_% ymm12) (%_% ymm12) *)
  0xc4; 0xc2; 0x15; 0x28; 0xc5;
                           (* VPMULDQ (%_% ymm0) (%_% ymm13) (%_% ymm13) *)
  0xc4; 0xc2; 0x0d; 0x28; 0xc6;
                           (* VPMULDQ (%_% ymm0) (%_% ymm14) (%_% ymm14) *)
  0xc4; 0x41; 0x7e; 0x16; 0xc0;
                           (* VMOVSHDUP (%_% ymm8) (%_% ymm8) *)
  0xc4; 0x43; 0x3d; 0x02; 0xe0; 0xaa;
                           (* VPBLENDD (%_% ymm12) (%_% ymm8) (%_% ymm8) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x5d; 0xfa; 0xc4;
                           (* VPSUBD (%_% ymm8) (%_% ymm4) (%_% ymm12) *)
  0xc5; 0x5d; 0xfe; 0xc4;  (* VPADDD (%_% ymm8) (%_% ymm4) (%_% ymm4) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xf5; 0xaa;
                           (* VPBLENDD (%_% ymm14) (%_% ymm13) (%_% ymm13) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x1d; 0xfe; 0xe8;
                           (* VPADDD (%_% ymm13) (%_% ymm12) (%_% ymm8) *)
  0xc5; 0x5d; 0xfa; 0xec;  (* VPSUBD (%_% ymm13) (%_% ymm4) (%_% ymm4) *)
  0xc4; 0xc2; 0x35; 0x28; 0xcd;
                           (* VPMULDQ (%_% ymm1) (%_% ymm9) (%_% ymm13) *)
  0xc4; 0x41; 0x7e; 0x16; 0xcc;
                           (* VMOVSHDUP (%_% ymm9) (%_% ymm12) *)
  0xc4; 0xc2; 0x1d; 0x28; 0xce;
                           (* VPMULDQ (%_% ymm1) (%_% ymm12) (%_% ymm14) *)
  0xc4; 0xc2; 0x35; 0x28; 0xd1;
                           (* VPMULDQ (%_% ymm2) (%_% ymm9) (%_% ymm9) *)
  0xc4; 0xc2; 0x1d; 0x28; 0xd4;
                           (* VPMULDQ (%_% ymm2) (%_% ymm12) (%_% ymm12) *)
  0xc4; 0xc2; 0x15; 0x28; 0xc5;
                           (* VPMULDQ (%_% ymm0) (%_% ymm13) (%_% ymm13) *)
  0xc4; 0xc2; 0x0d; 0x28; 0xc6;
                           (* VPMULDQ (%_% ymm0) (%_% ymm14) (%_% ymm14) *)
  0xc4; 0x41; 0x7e; 0x16; 0xc9;
                           (* VMOVSHDUP (%_% ymm9) (%_% ymm9) *)
  0xc4; 0x43; 0x35; 0x02; 0xe1; 0xaa;
                           (* VPBLENDD (%_% ymm12) (%_% ymm9) (%_% ymm9) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x55; 0xfa; 0xcc;
                           (* VPSUBD (%_% ymm9) (%_% ymm5) (%_% ymm12) *)
  0xc5; 0x55; 0xfe; 0xcd;  (* VPADDD (%_% ymm9) (%_% ymm5) (%_% ymm5) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xf5; 0xaa;
                           (* VPBLENDD (%_% ymm14) (%_% ymm13) (%_% ymm13) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x1d; 0xfe; 0xe9;
                           (* VPADDD (%_% ymm13) (%_% ymm12) (%_% ymm9) *)
  0xc5; 0x55; 0xfa; 0xed;  (* VPSUBD (%_% ymm13) (%_% ymm5) (%_% ymm5) *)
  0xc4; 0xc2; 0x2d; 0x28; 0xcd;
                           (* VPMULDQ (%_% ymm1) (%_% ymm10) (%_% ymm13) *)
  0xc4; 0x41; 0x7e; 0x16; 0xd4;
                           (* VMOVSHDUP (%_% ymm10) (%_% ymm12) *)
  0xc4; 0xc2; 0x1d; 0x28; 0xce;
                           (* VPMULDQ (%_% ymm1) (%_% ymm12) (%_% ymm14) *)
  0xc4; 0xc2; 0x2d; 0x28; 0xd2;
                           (* VPMULDQ (%_% ymm2) (%_% ymm10) (%_% ymm10) *)
  0xc4; 0xc2; 0x1d; 0x28; 0xd4;
                           (* VPMULDQ (%_% ymm2) (%_% ymm12) (%_% ymm12) *)
  0xc4; 0xc2; 0x15; 0x28; 0xc5;
                           (* VPMULDQ (%_% ymm0) (%_% ymm13) (%_% ymm13) *)
  0xc4; 0xc2; 0x0d; 0x28; 0xc6;
                           (* VPMULDQ (%_% ymm0) (%_% ymm14) (%_% ymm14) *)
  0xc4; 0x41; 0x7e; 0x16; 0xd2;
                           (* VMOVSHDUP (%_% ymm10) (%_% ymm10) *)
  0xc4; 0x43; 0x2d; 0x02; 0xe2; 0xaa;
                           (* VPBLENDD (%_% ymm12) (%_% ymm10) (%_% ymm10) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x4d; 0xfa; 0xd4;
                           (* VPSUBD (%_% ymm10) (%_% ymm6) (%_% ymm12) *)
  0xc5; 0x4d; 0xfe; 0xd6;  (* VPADDD (%_% ymm10) (%_% ymm6) (%_% ymm6) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xf5; 0xaa;
                           (* VPBLENDD (%_% ymm14) (%_% ymm13) (%_% ymm13) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x1d; 0xfe; 0xea;
                           (* VPADDD (%_% ymm13) (%_% ymm12) (%_% ymm10) *)
  0xc5; 0x4d; 0xfa; 0xee;  (* VPSUBD (%_% ymm13) (%_% ymm6) (%_% ymm6) *)
  0xc4; 0xc2; 0x25; 0x28; 0xcd;
                           (* VPMULDQ (%_% ymm1) (%_% ymm11) (%_% ymm13) *)
  0xc4; 0x41; 0x7e; 0x16; 0xdc;
                           (* VMOVSHDUP (%_% ymm11) (%_% ymm12) *)
  0xc4; 0xc2; 0x1d; 0x28; 0xce;
                           (* VPMULDQ (%_% ymm1) (%_% ymm12) (%_% ymm14) *)
  0xc4; 0xc2; 0x25; 0x28; 0xd3;
                           (* VPMULDQ (%_% ymm2) (%_% ymm11) (%_% ymm11) *)
  0xc4; 0xc2; 0x1d; 0x28; 0xd4;
                           (* VPMULDQ (%_% ymm2) (%_% ymm12) (%_% ymm12) *)
  0xc4; 0xc2; 0x15; 0x28; 0xc5;
                           (* VPMULDQ (%_% ymm0) (%_% ymm13) (%_% ymm13) *)
  0xc4; 0xc2; 0x0d; 0x28; 0xc6;
                           (* VPMULDQ (%_% ymm0) (%_% ymm14) (%_% ymm14) *)
  0xc4; 0x41; 0x7e; 0x16; 0xdb;
                           (* VMOVSHDUP (%_% ymm11) (%_% ymm11) *)
  0xc4; 0x43; 0x25; 0x02; 0xe3; 0xaa;
                           (* VPBLENDD (%_% ymm12) (%_% ymm11) (%_% ymm11) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x45; 0xfa; 0xdc;
                           (* VPSUBD (%_% ymm11) (%_% ymm7) (%_% ymm12) *)
  0xc5; 0x45; 0xfe; 0xdf;  (* VPADDD (%_% ymm11) (%_% ymm7) (%_% ymm7) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xf5; 0xaa;
                           (* VPBLENDD (%_% ymm14) (%_% ymm13) (%_% ymm13) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x1d; 0xfe; 0xeb;
                           (* VPADDD (%_% ymm13) (%_% ymm12) (%_% ymm11) *)
  0xc5; 0x45; 0xfa; 0xef;  (* VPSUBD (%_% ymm13) (%_% ymm7) (%_% ymm7) *)
  0xc4; 0xc3; 0x5d; 0x46; 0xd8; 0x20;
                           (* VPERM2I128 (%_% ymm3) (%_% ymm4) (%_% ymm8) (Imm8 (word 32)) *)
  0xc4; 0x43; 0x5d; 0x46; 0xc0; 0x31;
                           (* VPERM2I128 (%_% ymm8) (%_% ymm4) (%_% ymm8) (Imm8 (word 49)) *)
  0xc4; 0xc3; 0x55; 0x46; 0xe1; 0x20;
                           (* VPERM2I128 (%_% ymm4) (%_% ymm5) (%_% ymm9) (Imm8 (word 32)) *)
  0xc4; 0x43; 0x55; 0x46; 0xc9; 0x31;
                           (* VPERM2I128 (%_% ymm9) (%_% ymm5) (%_% ymm9) (Imm8 (word 49)) *)
  0xc4; 0xc3; 0x4d; 0x46; 0xea; 0x20;
                           (* VPERM2I128 (%_% ymm5) (%_% ymm6) (%_% ymm10) (Imm8 (word 32)) *)
  0xc4; 0x43; 0x4d; 0x46; 0xd2; 0x31;
                           (* VPERM2I128 (%_% ymm10) (%_% ymm6) (%_% ymm10) (Imm8 (word 49)) *)
  0xc4; 0xc3; 0x45; 0x46; 0xf3; 0x20;
                           (* VPERM2I128 (%_% ymm6) (%_% ymm7) (%_% ymm11) (Imm8 (word 32)) *)
  0xc4; 0x43; 0x45; 0x46; 0xdb; 0x31;
                           (* VPERM2I128 (%_% ymm11) (%_% ymm7) (%_% ymm11) (Imm8 (word 49)) *)
  0xc5; 0xfd; 0x6f; 0x8e; 0xe0; 0x00; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm1) (Memop Word256 (%% (rsi,224))) *)
  0xc5; 0xfd; 0x6f; 0x96; 0x80; 0x05; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm2) (Memop Word256 (%% (rsi,1408))) *)
  0xc4; 0xc2; 0x55; 0x28; 0xcd;
                           (* VPMULDQ (%_% ymm1) (%_% ymm5) (%_% ymm13) *)
  0xc4; 0xc1; 0x7e; 0x16; 0xec;
                           (* VMOVSHDUP (%_% ymm5) (%_% ymm12) *)
  0xc4; 0xc2; 0x1d; 0x28; 0xce;
                           (* VPMULDQ (%_% ymm1) (%_% ymm12) (%_% ymm14) *)
  0xc4; 0xe2; 0x55; 0x28; 0xd5;
                           (* VPMULDQ (%_% ymm2) (%_% ymm5) (%_% ymm5) *)
  0xc4; 0xc2; 0x1d; 0x28; 0xd4;
                           (* VPMULDQ (%_% ymm2) (%_% ymm12) (%_% ymm12) *)
  0xc4; 0xc2; 0x15; 0x28; 0xc5;
                           (* VPMULDQ (%_% ymm0) (%_% ymm13) (%_% ymm13) *)
  0xc4; 0xc2; 0x0d; 0x28; 0xc6;
                           (* VPMULDQ (%_% ymm0) (%_% ymm14) (%_% ymm14) *)
  0xc5; 0xfe; 0x16; 0xed;  (* VMOVSHDUP (%_% ymm5) (%_% ymm5) *)
  0xc4; 0x63; 0x55; 0x02; 0xe5; 0xaa;
                           (* VPBLENDD (%_% ymm12) (%_% ymm5) (%_% ymm5) (Imm8 (word 170)) *)
  0xc4; 0xc1; 0x65; 0xfa; 0xec;
                           (* VPSUBD (%_% ymm5) (%_% ymm3) (%_% ymm12) *)
  0xc5; 0xe5; 0xfe; 0xeb;  (* VPADDD (%_% ymm5) (%_% ymm3) (%_% ymm3) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xf5; 0xaa;
                           (* VPBLENDD (%_% ymm14) (%_% ymm13) (%_% ymm13) (Imm8 (word 170)) *)
  0xc5; 0x1d; 0xfe; 0xed;  (* VPADDD (%_% ymm13) (%_% ymm12) (%_% ymm5) *)
  0xc5; 0x65; 0xfa; 0xeb;  (* VPSUBD (%_% ymm13) (%_% ymm3) (%_% ymm3) *)
  0xc4; 0xc2; 0x2d; 0x28; 0xcd;
                           (* VPMULDQ (%_% ymm1) (%_% ymm10) (%_% ymm13) *)
  0xc4; 0x41; 0x7e; 0x16; 0xd4;
                           (* VMOVSHDUP (%_% ymm10) (%_% ymm12) *)
  0xc4; 0xc2; 0x1d; 0x28; 0xce;
                           (* VPMULDQ (%_% ymm1) (%_% ymm12) (%_% ymm14) *)
  0xc4; 0xc2; 0x2d; 0x28; 0xd2;
                           (* VPMULDQ (%_% ymm2) (%_% ymm10) (%_% ymm10) *)
  0xc4; 0xc2; 0x1d; 0x28; 0xd4;
                           (* VPMULDQ (%_% ymm2) (%_% ymm12) (%_% ymm12) *)
  0xc4; 0xc2; 0x15; 0x28; 0xc5;
                           (* VPMULDQ (%_% ymm0) (%_% ymm13) (%_% ymm13) *)
  0xc4; 0xc2; 0x0d; 0x28; 0xc6;
                           (* VPMULDQ (%_% ymm0) (%_% ymm14) (%_% ymm14) *)
  0xc4; 0x41; 0x7e; 0x16; 0xd2;
                           (* VMOVSHDUP (%_% ymm10) (%_% ymm10) *)
  0xc4; 0x43; 0x2d; 0x02; 0xe2; 0xaa;
                           (* VPBLENDD (%_% ymm12) (%_% ymm10) (%_% ymm10) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x3d; 0xfa; 0xd4;
                           (* VPSUBD (%_% ymm10) (%_% ymm8) (%_% ymm12) *)
  0xc4; 0x41; 0x3d; 0xfe; 0xd0;
                           (* VPADDD (%_% ymm10) (%_% ymm8) (%_% ymm8) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xf5; 0xaa;
                           (* VPBLENDD (%_% ymm14) (%_% ymm13) (%_% ymm13) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x1d; 0xfe; 0xea;
                           (* VPADDD (%_% ymm13) (%_% ymm12) (%_% ymm10) *)
  0xc4; 0x41; 0x3d; 0xfa; 0xe8;
                           (* VPSUBD (%_% ymm13) (%_% ymm8) (%_% ymm8) *)
  0xc4; 0xc2; 0x4d; 0x28; 0xcd;
                           (* VPMULDQ (%_% ymm1) (%_% ymm6) (%_% ymm13) *)
  0xc4; 0xc1; 0x7e; 0x16; 0xf4;
                           (* VMOVSHDUP (%_% ymm6) (%_% ymm12) *)
  0xc4; 0xc2; 0x1d; 0x28; 0xce;
                           (* VPMULDQ (%_% ymm1) (%_% ymm12) (%_% ymm14) *)
  0xc4; 0xe2; 0x4d; 0x28; 0xd6;
                           (* VPMULDQ (%_% ymm2) (%_% ymm6) (%_% ymm6) *)
  0xc4; 0xc2; 0x1d; 0x28; 0xd4;
                           (* VPMULDQ (%_% ymm2) (%_% ymm12) (%_% ymm12) *)
  0xc4; 0xc2; 0x15; 0x28; 0xc5;
                           (* VPMULDQ (%_% ymm0) (%_% ymm13) (%_% ymm13) *)
  0xc4; 0xc2; 0x0d; 0x28; 0xc6;
                           (* VPMULDQ (%_% ymm0) (%_% ymm14) (%_% ymm14) *)
  0xc5; 0xfe; 0x16; 0xf6;  (* VMOVSHDUP (%_% ymm6) (%_% ymm6) *)
  0xc4; 0x63; 0x4d; 0x02; 0xe6; 0xaa;
                           (* VPBLENDD (%_% ymm12) (%_% ymm6) (%_% ymm6) (Imm8 (word 170)) *)
  0xc4; 0xc1; 0x5d; 0xfa; 0xf4;
                           (* VPSUBD (%_% ymm6) (%_% ymm4) (%_% ymm12) *)
  0xc5; 0xdd; 0xfe; 0xf4;  (* VPADDD (%_% ymm6) (%_% ymm4) (%_% ymm4) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xf5; 0xaa;
                           (* VPBLENDD (%_% ymm14) (%_% ymm13) (%_% ymm13) (Imm8 (word 170)) *)
  0xc5; 0x1d; 0xfe; 0xee;  (* VPADDD (%_% ymm13) (%_% ymm12) (%_% ymm6) *)
  0xc5; 0x5d; 0xfa; 0xec;  (* VPSUBD (%_% ymm13) (%_% ymm4) (%_% ymm4) *)
  0xc4; 0xc2; 0x25; 0x28; 0xcd;
                           (* VPMULDQ (%_% ymm1) (%_% ymm11) (%_% ymm13) *)
  0xc4; 0x41; 0x7e; 0x16; 0xdc;
                           (* VMOVSHDUP (%_% ymm11) (%_% ymm12) *)
  0xc4; 0xc2; 0x1d; 0x28; 0xce;
                           (* VPMULDQ (%_% ymm1) (%_% ymm12) (%_% ymm14) *)
  0xc4; 0xc2; 0x25; 0x28; 0xd3;
                           (* VPMULDQ (%_% ymm2) (%_% ymm11) (%_% ymm11) *)
  0xc4; 0xc2; 0x1d; 0x28; 0xd4;
                           (* VPMULDQ (%_% ymm2) (%_% ymm12) (%_% ymm12) *)
  0xc4; 0xc2; 0x15; 0x28; 0xc5;
                           (* VPMULDQ (%_% ymm0) (%_% ymm13) (%_% ymm13) *)
  0xc4; 0xc2; 0x0d; 0x28; 0xc6;
                           (* VPMULDQ (%_% ymm0) (%_% ymm14) (%_% ymm14) *)
  0xc4; 0x41; 0x7e; 0x16; 0xdb;
                           (* VMOVSHDUP (%_% ymm11) (%_% ymm11) *)
  0xc4; 0x43; 0x25; 0x02; 0xe3; 0xaa;
                           (* VPBLENDD (%_% ymm12) (%_% ymm11) (%_% ymm11) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x35; 0xfa; 0xdc;
                           (* VPSUBD (%_% ymm11) (%_% ymm9) (%_% ymm12) *)
  0xc4; 0x41; 0x35; 0xfe; 0xd9;
                           (* VPADDD (%_% ymm11) (%_% ymm9) (%_% ymm9) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xf5; 0xaa;
                           (* VPBLENDD (%_% ymm14) (%_% ymm13) (%_% ymm13) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x1d; 0xfe; 0xeb;
                           (* VPADDD (%_% ymm13) (%_% ymm12) (%_% ymm11) *)
  0xc4; 0x41; 0x35; 0xfa; 0xe9;
                           (* VPSUBD (%_% ymm13) (%_% ymm9) (%_% ymm9) *)
  0xc5; 0xe5; 0x6c; 0xfd;  (* VPUNPCKLQDQ (%_% ymm7) (%_% ymm3) (%_% ymm5) *)
  0xc5; 0xe5; 0x6d; 0xed;  (* VPUNPCKHQDQ (%_% ymm5) (%_% ymm3) (%_% ymm5) *)
  0xc4; 0xc1; 0x3d; 0x6c; 0xda;
                           (* VPUNPCKLQDQ (%_% ymm3) (%_% ymm8) (%_% ymm10) *)
  0xc4; 0x41; 0x3d; 0x6d; 0xd2;
                           (* VPUNPCKHQDQ (%_% ymm10) (%_% ymm8) (%_% ymm10) *)
  0xc5; 0x5d; 0x6c; 0xc6;  (* VPUNPCKLQDQ (%_% ymm8) (%_% ymm4) (%_% ymm6) *)
  0xc5; 0xdd; 0x6d; 0xf6;  (* VPUNPCKHQDQ (%_% ymm6) (%_% ymm4) (%_% ymm6) *)
  0xc4; 0xc1; 0x35; 0x6c; 0xe3;
                           (* VPUNPCKLQDQ (%_% ymm4) (%_% ymm9) (%_% ymm11) *)
  0xc4; 0x41; 0x35; 0x6d; 0xdb;
                           (* VPUNPCKHQDQ (%_% ymm11) (%_% ymm9) (%_% ymm11) *)
  0xc5; 0xfd; 0x6f; 0x8e; 0x60; 0x01; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm1) (Memop Word256 (%% (rsi,352))) *)
  0xc5; 0xfd; 0x6f; 0x96; 0x00; 0x06; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm2) (Memop Word256 (%% (rsi,1536))) *)
  0xc4; 0xc2; 0x3d; 0x28; 0xcd;
                           (* VPMULDQ (%_% ymm1) (%_% ymm8) (%_% ymm13) *)
  0xc4; 0x41; 0x7e; 0x16; 0xc4;
                           (* VMOVSHDUP (%_% ymm8) (%_% ymm12) *)
  0xc4; 0xc2; 0x1d; 0x28; 0xce;
                           (* VPMULDQ (%_% ymm1) (%_% ymm12) (%_% ymm14) *)
  0xc4; 0xc2; 0x3d; 0x28; 0xd0;
                           (* VPMULDQ (%_% ymm2) (%_% ymm8) (%_% ymm8) *)
  0xc4; 0xc2; 0x1d; 0x28; 0xd4;
                           (* VPMULDQ (%_% ymm2) (%_% ymm12) (%_% ymm12) *)
  0xc4; 0xc2; 0x15; 0x28; 0xc5;
                           (* VPMULDQ (%_% ymm0) (%_% ymm13) (%_% ymm13) *)
  0xc4; 0xc2; 0x0d; 0x28; 0xc6;
                           (* VPMULDQ (%_% ymm0) (%_% ymm14) (%_% ymm14) *)
  0xc4; 0x41; 0x7e; 0x16; 0xc0;
                           (* VMOVSHDUP (%_% ymm8) (%_% ymm8) *)
  0xc4; 0x43; 0x3d; 0x02; 0xe0; 0xaa;
                           (* VPBLENDD (%_% ymm12) (%_% ymm8) (%_% ymm8) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x45; 0xfa; 0xc4;
                           (* VPSUBD (%_% ymm8) (%_% ymm7) (%_% ymm12) *)
  0xc5; 0x45; 0xfe; 0xc7;  (* VPADDD (%_% ymm8) (%_% ymm7) (%_% ymm7) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xf5; 0xaa;
                           (* VPBLENDD (%_% ymm14) (%_% ymm13) (%_% ymm13) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x1d; 0xfe; 0xe8;
                           (* VPADDD (%_% ymm13) (%_% ymm12) (%_% ymm8) *)
  0xc5; 0x45; 0xfa; 0xef;  (* VPSUBD (%_% ymm13) (%_% ymm7) (%_% ymm7) *)
  0xc4; 0xc2; 0x4d; 0x28; 0xcd;
                           (* VPMULDQ (%_% ymm1) (%_% ymm6) (%_% ymm13) *)
  0xc4; 0xc1; 0x7e; 0x16; 0xf4;
                           (* VMOVSHDUP (%_% ymm6) (%_% ymm12) *)
  0xc4; 0xc2; 0x1d; 0x28; 0xce;
                           (* VPMULDQ (%_% ymm1) (%_% ymm12) (%_% ymm14) *)
  0xc4; 0xe2; 0x4d; 0x28; 0xd6;
                           (* VPMULDQ (%_% ymm2) (%_% ymm6) (%_% ymm6) *)
  0xc4; 0xc2; 0x1d; 0x28; 0xd4;
                           (* VPMULDQ (%_% ymm2) (%_% ymm12) (%_% ymm12) *)
  0xc4; 0xc2; 0x15; 0x28; 0xc5;
                           (* VPMULDQ (%_% ymm0) (%_% ymm13) (%_% ymm13) *)
  0xc4; 0xc2; 0x0d; 0x28; 0xc6;
                           (* VPMULDQ (%_% ymm0) (%_% ymm14) (%_% ymm14) *)
  0xc5; 0xfe; 0x16; 0xf6;  (* VMOVSHDUP (%_% ymm6) (%_% ymm6) *)
  0xc4; 0x63; 0x4d; 0x02; 0xe6; 0xaa;
                           (* VPBLENDD (%_% ymm12) (%_% ymm6) (%_% ymm6) (Imm8 (word 170)) *)
  0xc4; 0xc1; 0x55; 0xfa; 0xf4;
                           (* VPSUBD (%_% ymm6) (%_% ymm5) (%_% ymm12) *)
  0xc5; 0xd5; 0xfe; 0xf5;  (* VPADDD (%_% ymm6) (%_% ymm5) (%_% ymm5) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xf5; 0xaa;
                           (* VPBLENDD (%_% ymm14) (%_% ymm13) (%_% ymm13) (Imm8 (word 170)) *)
  0xc5; 0x1d; 0xfe; 0xee;  (* VPADDD (%_% ymm13) (%_% ymm12) (%_% ymm6) *)
  0xc5; 0x55; 0xfa; 0xed;  (* VPSUBD (%_% ymm13) (%_% ymm5) (%_% ymm5) *)
  0xc4; 0xc2; 0x5d; 0x28; 0xcd;
                           (* VPMULDQ (%_% ymm1) (%_% ymm4) (%_% ymm13) *)
  0xc4; 0xc1; 0x7e; 0x16; 0xe4;
                           (* VMOVSHDUP (%_% ymm4) (%_% ymm12) *)
  0xc4; 0xc2; 0x1d; 0x28; 0xce;
                           (* VPMULDQ (%_% ymm1) (%_% ymm12) (%_% ymm14) *)
  0xc4; 0xe2; 0x5d; 0x28; 0xd4;
                           (* VPMULDQ (%_% ymm2) (%_% ymm4) (%_% ymm4) *)
  0xc4; 0xc2; 0x1d; 0x28; 0xd4;
                           (* VPMULDQ (%_% ymm2) (%_% ymm12) (%_% ymm12) *)
  0xc4; 0xc2; 0x15; 0x28; 0xc5;
                           (* VPMULDQ (%_% ymm0) (%_% ymm13) (%_% ymm13) *)
  0xc4; 0xc2; 0x0d; 0x28; 0xc6;
                           (* VPMULDQ (%_% ymm0) (%_% ymm14) (%_% ymm14) *)
  0xc5; 0xfe; 0x16; 0xe4;  (* VMOVSHDUP (%_% ymm4) (%_% ymm4) *)
  0xc4; 0x63; 0x5d; 0x02; 0xe4; 0xaa;
                           (* VPBLENDD (%_% ymm12) (%_% ymm4) (%_% ymm4) (Imm8 (word 170)) *)
  0xc4; 0xc1; 0x65; 0xfa; 0xe4;
                           (* VPSUBD (%_% ymm4) (%_% ymm3) (%_% ymm12) *)
  0xc5; 0xe5; 0xfe; 0xe3;  (* VPADDD (%_% ymm4) (%_% ymm3) (%_% ymm3) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xf5; 0xaa;
                           (* VPBLENDD (%_% ymm14) (%_% ymm13) (%_% ymm13) (Imm8 (word 170)) *)
  0xc5; 0x1d; 0xfe; 0xec;  (* VPADDD (%_% ymm13) (%_% ymm12) (%_% ymm4) *)
  0xc5; 0x65; 0xfa; 0xeb;  (* VPSUBD (%_% ymm13) (%_% ymm3) (%_% ymm3) *)
  0xc4; 0xc2; 0x25; 0x28; 0xcd;
                           (* VPMULDQ (%_% ymm1) (%_% ymm11) (%_% ymm13) *)
  0xc4; 0x41; 0x7e; 0x16; 0xdc;
                           (* VMOVSHDUP (%_% ymm11) (%_% ymm12) *)
  0xc4; 0xc2; 0x1d; 0x28; 0xce;
                           (* VPMULDQ (%_% ymm1) (%_% ymm12) (%_% ymm14) *)
  0xc4; 0xc2; 0x25; 0x28; 0xd3;
                           (* VPMULDQ (%_% ymm2) (%_% ymm11) (%_% ymm11) *)
  0xc4; 0xc2; 0x1d; 0x28; 0xd4;
                           (* VPMULDQ (%_% ymm2) (%_% ymm12) (%_% ymm12) *)
  0xc4; 0xc2; 0x15; 0x28; 0xc5;
                           (* VPMULDQ (%_% ymm0) (%_% ymm13) (%_% ymm13) *)
  0xc4; 0xc2; 0x0d; 0x28; 0xc6;
                           (* VPMULDQ (%_% ymm0) (%_% ymm14) (%_% ymm14) *)
  0xc4; 0x41; 0x7e; 0x16; 0xdb;
                           (* VMOVSHDUP (%_% ymm11) (%_% ymm11) *)
  0xc4; 0x43; 0x25; 0x02; 0xe3; 0xaa;
                           (* VPBLENDD (%_% ymm12) (%_% ymm11) (%_% ymm11) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x2d; 0xfa; 0xdc;
                           (* VPSUBD (%_% ymm11) (%_% ymm10) (%_% ymm12) *)
  0xc4; 0x41; 0x2d; 0xfe; 0xda;
                           (* VPADDD (%_% ymm11) (%_% ymm10) (%_% ymm10) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xf5; 0xaa;
                           (* VPBLENDD (%_% ymm14) (%_% ymm13) (%_% ymm13) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x1d; 0xfe; 0xeb;
                           (* VPADDD (%_% ymm13) (%_% ymm12) (%_% ymm11) *)
  0xc4; 0x41; 0x2d; 0xfa; 0xea;
                           (* VPSUBD (%_% ymm13) (%_% ymm10) (%_% ymm10) *)
  0xc4; 0x41; 0x7e; 0x12; 0xc8;
                           (* VMOVSLDUP (%_% ymm9) (%_% ymm8) *)
  0xc4; 0x63; 0x35; 0x02; 0xcf; 0xaa;
                           (* VPBLENDD (%_% ymm9) (%_% ymm9) (%_% ymm7) (Imm8 (word 170)) *)
  0xc5; 0xc5; 0x73; 0xd7; 0x20;
                           (* VPSRLQ (%_% ymm7) (%_% ymm7) (Imm8 (word 32)) *)
  0xc4; 0x63; 0x3d; 0x02; 0xc7; 0xaa;
                           (* VPBLENDD (%_% ymm8) (%_% ymm8) (%_% ymm7) (Imm8 (word 170)) *)
  0xc5; 0xfe; 0x12; 0xfe;  (* VMOVSLDUP (%_% ymm7) (%_% ymm6) *)
  0xc4; 0xe3; 0x45; 0x02; 0xfd; 0xaa;
                           (* VPBLENDD (%_% ymm7) (%_% ymm7) (%_% ymm5) (Imm8 (word 170)) *)
  0xc5; 0xd5; 0x73; 0xd5; 0x20;
                           (* VPSRLQ (%_% ymm5) (%_% ymm5) (Imm8 (word 32)) *)
  0xc4; 0xe3; 0x4d; 0x02; 0xf5; 0xaa;
                           (* VPBLENDD (%_% ymm6) (%_% ymm6) (%_% ymm5) (Imm8 (word 170)) *)
  0xc5; 0xfe; 0x12; 0xec;  (* VMOVSLDUP (%_% ymm5) (%_% ymm4) *)
  0xc4; 0xe3; 0x55; 0x02; 0xeb; 0xaa;
                           (* VPBLENDD (%_% ymm5) (%_% ymm5) (%_% ymm3) (Imm8 (word 170)) *)
  0xc5; 0xe5; 0x73; 0xd3; 0x20;
                           (* VPSRLQ (%_% ymm3) (%_% ymm3) (Imm8 (word 32)) *)
  0xc4; 0xe3; 0x5d; 0x02; 0xe3; 0xaa;
                           (* VPBLENDD (%_% ymm4) (%_% ymm4) (%_% ymm3) (Imm8 (word 170)) *)
  0xc4; 0xc1; 0x7e; 0x12; 0xdb;
                           (* VMOVSLDUP (%_% ymm3) (%_% ymm11) *)
  0xc4; 0xc3; 0x65; 0x02; 0xda; 0xaa;
                           (* VPBLENDD (%_% ymm3) (%_% ymm3) (%_% ymm10) (Imm8 (word 170)) *)
  0xc4; 0xc1; 0x2d; 0x73; 0xd2; 0x20;
                           (* VPSRLQ (%_% ymm10) (%_% ymm10) (Imm8 (word 32)) *)
  0xc4; 0x43; 0x25; 0x02; 0xda; 0xaa;
                           (* VPBLENDD (%_% ymm11) (%_% ymm11) (%_% ymm10) (Imm8 (word 170)) *)
  0xc5; 0xfd; 0x6f; 0x8e; 0xe0; 0x01; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm1) (Memop Word256 (%% (rsi,480))) *)
  0xc5; 0xfd; 0x6f; 0x96; 0x80; 0x06; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm2) (Memop Word256 (%% (rsi,1664))) *)
  0xc4; 0xc1; 0x75; 0x73; 0xd2; 0x20;
                           (* VPSRLQ (%_% ymm1) (%_% ymm10) (Imm8 (word 32)) *)
  0xc4; 0xc1; 0x7e; 0x16; 0xd7;
                           (* VMOVSHDUP (%_% ymm2) (%_% ymm15) *)
  0xc4; 0xc2; 0x55; 0x28; 0xcd;
                           (* VPMULDQ (%_% ymm1) (%_% ymm5) (%_% ymm13) *)
  0xc4; 0xc1; 0x7e; 0x16; 0xec;
                           (* VMOVSHDUP (%_% ymm5) (%_% ymm12) *)
  0xc4; 0x42; 0x1d; 0x28; 0xd6;
                           (* VPMULDQ (%_% ymm10) (%_% ymm12) (%_% ymm14) *)
  0xc4; 0xe2; 0x55; 0x28; 0xd5;
                           (* VPMULDQ (%_% ymm2) (%_% ymm5) (%_% ymm5) *)
  0xc4; 0x42; 0x1d; 0x28; 0xfc;
                           (* VPMULDQ (%_% ymm15) (%_% ymm12) (%_% ymm12) *)
  0xc4; 0xc2; 0x15; 0x28; 0xc5;
                           (* VPMULDQ (%_% ymm0) (%_% ymm13) (%_% ymm13) *)
  0xc4; 0xc2; 0x0d; 0x28; 0xc6;
                           (* VPMULDQ (%_% ymm0) (%_% ymm14) (%_% ymm14) *)
  0xc5; 0xfe; 0x16; 0xed;  (* VMOVSHDUP (%_% ymm5) (%_% ymm5) *)
  0xc4; 0x63; 0x55; 0x02; 0xe5; 0xaa;
                           (* VPBLENDD (%_% ymm12) (%_% ymm5) (%_% ymm5) (Imm8 (word 170)) *)
  0xc4; 0xc1; 0x35; 0xfa; 0xec;
                           (* VPSUBD (%_% ymm5) (%_% ymm9) (%_% ymm12) *)
  0xc4; 0xc1; 0x35; 0xfe; 0xe9;
                           (* VPADDD (%_% ymm5) (%_% ymm9) (%_% ymm9) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xf5; 0xaa;
                           (* VPBLENDD (%_% ymm14) (%_% ymm13) (%_% ymm13) (Imm8 (word 170)) *)
  0xc5; 0x1d; 0xfe; 0xed;  (* VPADDD (%_% ymm13) (%_% ymm12) (%_% ymm5) *)
  0xc4; 0x41; 0x35; 0xfa; 0xe9;
                           (* VPSUBD (%_% ymm13) (%_% ymm9) (%_% ymm9) *)
  0xc4; 0xc2; 0x5d; 0x28; 0xcd;
                           (* VPMULDQ (%_% ymm1) (%_% ymm4) (%_% ymm13) *)
  0xc4; 0xc1; 0x7e; 0x16; 0xe4;
                           (* VMOVSHDUP (%_% ymm4) (%_% ymm12) *)
  0xc4; 0x42; 0x1d; 0x28; 0xd6;
                           (* VPMULDQ (%_% ymm10) (%_% ymm12) (%_% ymm14) *)
  0xc4; 0xe2; 0x5d; 0x28; 0xd4;
                           (* VPMULDQ (%_% ymm2) (%_% ymm4) (%_% ymm4) *)
  0xc4; 0x42; 0x1d; 0x28; 0xfc;
                           (* VPMULDQ (%_% ymm15) (%_% ymm12) (%_% ymm12) *)
  0xc4; 0xc2; 0x15; 0x28; 0xc5;
                           (* VPMULDQ (%_% ymm0) (%_% ymm13) (%_% ymm13) *)
  0xc4; 0xc2; 0x0d; 0x28; 0xc6;
                           (* VPMULDQ (%_% ymm0) (%_% ymm14) (%_% ymm14) *)
  0xc5; 0xfe; 0x16; 0xe4;  (* VMOVSHDUP (%_% ymm4) (%_% ymm4) *)
  0xc4; 0x63; 0x5d; 0x02; 0xe4; 0xaa;
                           (* VPBLENDD (%_% ymm12) (%_% ymm4) (%_% ymm4) (Imm8 (word 170)) *)
  0xc4; 0xc1; 0x3d; 0xfa; 0xe4;
                           (* VPSUBD (%_% ymm4) (%_% ymm8) (%_% ymm12) *)
  0xc4; 0xc1; 0x3d; 0xfe; 0xe0;
                           (* VPADDD (%_% ymm4) (%_% ymm8) (%_% ymm8) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xf5; 0xaa;
                           (* VPBLENDD (%_% ymm14) (%_% ymm13) (%_% ymm13) (Imm8 (word 170)) *)
  0xc5; 0x1d; 0xfe; 0xec;  (* VPADDD (%_% ymm13) (%_% ymm12) (%_% ymm4) *)
  0xc4; 0x41; 0x3d; 0xfa; 0xe8;
                           (* VPSUBD (%_% ymm13) (%_% ymm8) (%_% ymm8) *)
  0xc4; 0xc2; 0x65; 0x28; 0xcd;
                           (* VPMULDQ (%_% ymm1) (%_% ymm3) (%_% ymm13) *)
  0xc4; 0xc1; 0x7e; 0x16; 0xdc;
                           (* VMOVSHDUP (%_% ymm3) (%_% ymm12) *)
  0xc4; 0x42; 0x1d; 0x28; 0xd6;
                           (* VPMULDQ (%_% ymm10) (%_% ymm12) (%_% ymm14) *)
  0xc4; 0xe2; 0x65; 0x28; 0xd3;
                           (* VPMULDQ (%_% ymm2) (%_% ymm3) (%_% ymm3) *)
  0xc4; 0x42; 0x1d; 0x28; 0xfc;
                           (* VPMULDQ (%_% ymm15) (%_% ymm12) (%_% ymm12) *)
  0xc4; 0xc2; 0x15; 0x28; 0xc5;
                           (* VPMULDQ (%_% ymm0) (%_% ymm13) (%_% ymm13) *)
  0xc4; 0xc2; 0x0d; 0x28; 0xc6;
                           (* VPMULDQ (%_% ymm0) (%_% ymm14) (%_% ymm14) *)
  0xc5; 0xfe; 0x16; 0xdb;  (* VMOVSHDUP (%_% ymm3) (%_% ymm3) *)
  0xc4; 0x63; 0x65; 0x02; 0xe3; 0xaa;
                           (* VPBLENDD (%_% ymm12) (%_% ymm3) (%_% ymm3) (Imm8 (word 170)) *)
  0xc4; 0xc1; 0x45; 0xfa; 0xdc;
                           (* VPSUBD (%_% ymm3) (%_% ymm7) (%_% ymm12) *)
  0xc5; 0xc5; 0xfe; 0xdf;  (* VPADDD (%_% ymm3) (%_% ymm7) (%_% ymm7) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xf5; 0xaa;
                           (* VPBLENDD (%_% ymm14) (%_% ymm13) (%_% ymm13) (Imm8 (word 170)) *)
  0xc5; 0x1d; 0xfe; 0xeb;  (* VPADDD (%_% ymm13) (%_% ymm12) (%_% ymm3) *)
  0xc5; 0x45; 0xfa; 0xef;  (* VPSUBD (%_% ymm13) (%_% ymm7) (%_% ymm7) *)
  0xc4; 0xc2; 0x25; 0x28; 0xcd;
                           (* VPMULDQ (%_% ymm1) (%_% ymm11) (%_% ymm13) *)
  0xc4; 0x41; 0x7e; 0x16; 0xdc;
                           (* VMOVSHDUP (%_% ymm11) (%_% ymm12) *)
  0xc4; 0x42; 0x1d; 0x28; 0xd6;
                           (* VPMULDQ (%_% ymm10) (%_% ymm12) (%_% ymm14) *)
  0xc4; 0xc2; 0x25; 0x28; 0xd3;
                           (* VPMULDQ (%_% ymm2) (%_% ymm11) (%_% ymm11) *)
  0xc4; 0x42; 0x1d; 0x28; 0xfc;
                           (* VPMULDQ (%_% ymm15) (%_% ymm12) (%_% ymm12) *)
  0xc4; 0xc2; 0x15; 0x28; 0xc5;
                           (* VPMULDQ (%_% ymm0) (%_% ymm13) (%_% ymm13) *)
  0xc4; 0xc2; 0x0d; 0x28; 0xc6;
                           (* VPMULDQ (%_% ymm0) (%_% ymm14) (%_% ymm14) *)
  0xc4; 0x41; 0x7e; 0x16; 0xdb;
                           (* VMOVSHDUP (%_% ymm11) (%_% ymm11) *)
  0xc4; 0x43; 0x25; 0x02; 0xe3; 0xaa;
                           (* VPBLENDD (%_% ymm12) (%_% ymm11) (%_% ymm11) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x4d; 0xfa; 0xdc;
                           (* VPSUBD (%_% ymm11) (%_% ymm6) (%_% ymm12) *)
  0xc5; 0x4d; 0xfe; 0xde;  (* VPADDD (%_% ymm11) (%_% ymm6) (%_% ymm6) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xf5; 0xaa;
                           (* VPBLENDD (%_% ymm14) (%_% ymm13) (%_% ymm13) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x1d; 0xfe; 0xeb;
                           (* VPADDD (%_% ymm13) (%_% ymm12) (%_% ymm11) *)
  0xc5; 0x4d; 0xfa; 0xee;  (* VPSUBD (%_% ymm13) (%_% ymm6) (%_% ymm6) *)
  0xc5; 0xfd; 0x6f; 0x8e; 0x60; 0x02; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm1) (Memop Word256 (%% (rsi,608))) *)
  0xc5; 0xfd; 0x6f; 0x96; 0x00; 0x07; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm2) (Memop Word256 (%% (rsi,1792))) *)
  0xc4; 0xc1; 0x75; 0x73; 0xd2; 0x20;
                           (* VPSRLQ (%_% ymm1) (%_% ymm10) (Imm8 (word 32)) *)
  0xc4; 0xc1; 0x7e; 0x16; 0xd7;
                           (* VMOVSHDUP (%_% ymm2) (%_% ymm15) *)
  0xc4; 0xc2; 0x45; 0x28; 0xcd;
                           (* VPMULDQ (%_% ymm1) (%_% ymm7) (%_% ymm13) *)
  0xc4; 0xc1; 0x7e; 0x16; 0xfc;
                           (* VMOVSHDUP (%_% ymm7) (%_% ymm12) *)
  0xc4; 0x42; 0x1d; 0x28; 0xd6;
                           (* VPMULDQ (%_% ymm10) (%_% ymm12) (%_% ymm14) *)
  0xc4; 0xe2; 0x45; 0x28; 0xd7;
                           (* VPMULDQ (%_% ymm2) (%_% ymm7) (%_% ymm7) *)
  0xc4; 0x42; 0x1d; 0x28; 0xfc;
                           (* VPMULDQ (%_% ymm15) (%_% ymm12) (%_% ymm12) *)
  0xc4; 0xc2; 0x15; 0x28; 0xc5;
                           (* VPMULDQ (%_% ymm0) (%_% ymm13) (%_% ymm13) *)
  0xc4; 0xc2; 0x0d; 0x28; 0xc6;
                           (* VPMULDQ (%_% ymm0) (%_% ymm14) (%_% ymm14) *)
  0xc5; 0xfe; 0x16; 0xff;  (* VMOVSHDUP (%_% ymm7) (%_% ymm7) *)
  0xc4; 0x63; 0x45; 0x02; 0xe7; 0xaa;
                           (* VPBLENDD (%_% ymm12) (%_% ymm7) (%_% ymm7) (Imm8 (word 170)) *)
  0xc4; 0xc1; 0x35; 0xfa; 0xfc;
                           (* VPSUBD (%_% ymm7) (%_% ymm9) (%_% ymm12) *)
  0xc4; 0xc1; 0x35; 0xfe; 0xf9;
                           (* VPADDD (%_% ymm7) (%_% ymm9) (%_% ymm9) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xf5; 0xaa;
                           (* VPBLENDD (%_% ymm14) (%_% ymm13) (%_% ymm13) (Imm8 (word 170)) *)
  0xc5; 0x1d; 0xfe; 0xef;  (* VPADDD (%_% ymm13) (%_% ymm12) (%_% ymm7) *)
  0xc4; 0x41; 0x35; 0xfa; 0xe9;
                           (* VPSUBD (%_% ymm13) (%_% ymm9) (%_% ymm9) *)
  0xc4; 0xc2; 0x4d; 0x28; 0xcd;
                           (* VPMULDQ (%_% ymm1) (%_% ymm6) (%_% ymm13) *)
  0xc4; 0xc1; 0x7e; 0x16; 0xf4;
                           (* VMOVSHDUP (%_% ymm6) (%_% ymm12) *)
  0xc4; 0x42; 0x1d; 0x28; 0xd6;
                           (* VPMULDQ (%_% ymm10) (%_% ymm12) (%_% ymm14) *)
  0xc4; 0xe2; 0x4d; 0x28; 0xd6;
                           (* VPMULDQ (%_% ymm2) (%_% ymm6) (%_% ymm6) *)
  0xc4; 0x42; 0x1d; 0x28; 0xfc;
                           (* VPMULDQ (%_% ymm15) (%_% ymm12) (%_% ymm12) *)
  0xc4; 0xc2; 0x15; 0x28; 0xc5;
                           (* VPMULDQ (%_% ymm0) (%_% ymm13) (%_% ymm13) *)
  0xc4; 0xc2; 0x0d; 0x28; 0xc6;
                           (* VPMULDQ (%_% ymm0) (%_% ymm14) (%_% ymm14) *)
  0xc5; 0xfe; 0x16; 0xf6;  (* VMOVSHDUP (%_% ymm6) (%_% ymm6) *)
  0xc4; 0x63; 0x4d; 0x02; 0xe6; 0xaa;
                           (* VPBLENDD (%_% ymm12) (%_% ymm6) (%_% ymm6) (Imm8 (word 170)) *)
  0xc4; 0xc1; 0x3d; 0xfa; 0xf4;
                           (* VPSUBD (%_% ymm6) (%_% ymm8) (%_% ymm12) *)
  0xc4; 0xc1; 0x3d; 0xfe; 0xf0;
                           (* VPADDD (%_% ymm6) (%_% ymm8) (%_% ymm8) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xf5; 0xaa;
                           (* VPBLENDD (%_% ymm14) (%_% ymm13) (%_% ymm13) (Imm8 (word 170)) *)
  0xc5; 0x1d; 0xfe; 0xee;  (* VPADDD (%_% ymm13) (%_% ymm12) (%_% ymm6) *)
  0xc4; 0x41; 0x3d; 0xfa; 0xe8;
                           (* VPSUBD (%_% ymm13) (%_% ymm8) (%_% ymm8) *)
  0xc5; 0xfd; 0x6f; 0x8e; 0xe0; 0x02; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm1) (Memop Word256 (%% (rsi,736))) *)
  0xc5; 0xfd; 0x6f; 0x96; 0x80; 0x07; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm2) (Memop Word256 (%% (rsi,1920))) *)
  0xc4; 0xc1; 0x75; 0x73; 0xd2; 0x20;
                           (* VPSRLQ (%_% ymm1) (%_% ymm10) (Imm8 (word 32)) *)
  0xc4; 0xc1; 0x7e; 0x16; 0xd7;
                           (* VMOVSHDUP (%_% ymm2) (%_% ymm15) *)
  0xc4; 0xc2; 0x65; 0x28; 0xcd;
                           (* VPMULDQ (%_% ymm1) (%_% ymm3) (%_% ymm13) *)
  0xc4; 0xc1; 0x7e; 0x16; 0xdc;
                           (* VMOVSHDUP (%_% ymm3) (%_% ymm12) *)
  0xc4; 0x42; 0x1d; 0x28; 0xd6;
                           (* VPMULDQ (%_% ymm10) (%_% ymm12) (%_% ymm14) *)
  0xc4; 0xe2; 0x65; 0x28; 0xd3;
                           (* VPMULDQ (%_% ymm2) (%_% ymm3) (%_% ymm3) *)
  0xc4; 0x42; 0x1d; 0x28; 0xfc;
                           (* VPMULDQ (%_% ymm15) (%_% ymm12) (%_% ymm12) *)
  0xc4; 0xc2; 0x15; 0x28; 0xc5;
                           (* VPMULDQ (%_% ymm0) (%_% ymm13) (%_% ymm13) *)
  0xc4; 0xc2; 0x0d; 0x28; 0xc6;
                           (* VPMULDQ (%_% ymm0) (%_% ymm14) (%_% ymm14) *)
  0xc5; 0xfe; 0x16; 0xdb;  (* VMOVSHDUP (%_% ymm3) (%_% ymm3) *)
  0xc4; 0x63; 0x65; 0x02; 0xe3; 0xaa;
                           (* VPBLENDD (%_% ymm12) (%_% ymm3) (%_% ymm3) (Imm8 (word 170)) *)
  0xc4; 0xc1; 0x55; 0xfa; 0xdc;
                           (* VPSUBD (%_% ymm3) (%_% ymm5) (%_% ymm12) *)
  0xc5; 0xd5; 0xfe; 0xdd;  (* VPADDD (%_% ymm3) (%_% ymm5) (%_% ymm5) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xf5; 0xaa;
                           (* VPBLENDD (%_% ymm14) (%_% ymm13) (%_% ymm13) (Imm8 (word 170)) *)
  0xc5; 0x1d; 0xfe; 0xeb;  (* VPADDD (%_% ymm13) (%_% ymm12) (%_% ymm3) *)
  0xc5; 0x55; 0xfa; 0xed;  (* VPSUBD (%_% ymm13) (%_% ymm5) (%_% ymm5) *)
  0xc4; 0xc2; 0x25; 0x28; 0xcd;
                           (* VPMULDQ (%_% ymm1) (%_% ymm11) (%_% ymm13) *)
  0xc4; 0x41; 0x7e; 0x16; 0xdc;
                           (* VMOVSHDUP (%_% ymm11) (%_% ymm12) *)
  0xc4; 0x42; 0x1d; 0x28; 0xd6;
                           (* VPMULDQ (%_% ymm10) (%_% ymm12) (%_% ymm14) *)
  0xc4; 0xc2; 0x25; 0x28; 0xd3;
                           (* VPMULDQ (%_% ymm2) (%_% ymm11) (%_% ymm11) *)
  0xc4; 0x42; 0x1d; 0x28; 0xfc;
                           (* VPMULDQ (%_% ymm15) (%_% ymm12) (%_% ymm12) *)
  0xc4; 0xc2; 0x15; 0x28; 0xc5;
                           (* VPMULDQ (%_% ymm0) (%_% ymm13) (%_% ymm13) *)
  0xc4; 0xc2; 0x0d; 0x28; 0xc6;
                           (* VPMULDQ (%_% ymm0) (%_% ymm14) (%_% ymm14) *)
  0xc4; 0x41; 0x7e; 0x16; 0xdb;
                           (* VMOVSHDUP (%_% ymm11) (%_% ymm11) *)
  0xc4; 0x43; 0x25; 0x02; 0xe3; 0xaa;
                           (* VPBLENDD (%_% ymm12) (%_% ymm11) (%_% ymm11) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x5d; 0xfa; 0xdc;
                           (* VPSUBD (%_% ymm11) (%_% ymm4) (%_% ymm12) *)
  0xc5; 0x5d; 0xfe; 0xdc;  (* VPADDD (%_% ymm11) (%_% ymm4) (%_% ymm4) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xf5; 0xaa;
                           (* VPBLENDD (%_% ymm14) (%_% ymm13) (%_% ymm13) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x1d; 0xfe; 0xeb;
                           (* VPADDD (%_% ymm13) (%_% ymm12) (%_% ymm11) *)
  0xc5; 0x5d; 0xfa; 0xec;  (* VPSUBD (%_% ymm13) (%_% ymm4) (%_% ymm4) *)
  0xc5; 0xfd; 0x6f; 0x8e; 0x60; 0x03; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm1) (Memop Word256 (%% (rsi,864))) *)
  0xc5; 0xfd; 0x6f; 0x96; 0x00; 0x08; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm2) (Memop Word256 (%% (rsi,2048))) *)
  0xc4; 0xc1; 0x75; 0x73; 0xd2; 0x20;
                           (* VPSRLQ (%_% ymm1) (%_% ymm10) (Imm8 (word 32)) *)
  0xc4; 0xc1; 0x7e; 0x16; 0xd7;
                           (* VMOVSHDUP (%_% ymm2) (%_% ymm15) *)
  0xc4; 0xc2; 0x3d; 0x28; 0xcd;
                           (* VPMULDQ (%_% ymm1) (%_% ymm8) (%_% ymm13) *)
  0xc4; 0x41; 0x7e; 0x16; 0xc4;
                           (* VMOVSHDUP (%_% ymm8) (%_% ymm12) *)
  0xc4; 0x42; 0x1d; 0x28; 0xd6;
                           (* VPMULDQ (%_% ymm10) (%_% ymm12) (%_% ymm14) *)
  0xc4; 0xc2; 0x3d; 0x28; 0xd0;
                           (* VPMULDQ (%_% ymm2) (%_% ymm8) (%_% ymm8) *)
  0xc4; 0x42; 0x1d; 0x28; 0xfc;
                           (* VPMULDQ (%_% ymm15) (%_% ymm12) (%_% ymm12) *)
  0xc4; 0xc2; 0x15; 0x28; 0xc5;
                           (* VPMULDQ (%_% ymm0) (%_% ymm13) (%_% ymm13) *)
  0xc4; 0xc2; 0x0d; 0x28; 0xc6;
                           (* VPMULDQ (%_% ymm0) (%_% ymm14) (%_% ymm14) *)
  0xc4; 0x41; 0x7e; 0x16; 0xc0;
                           (* VMOVSHDUP (%_% ymm8) (%_% ymm8) *)
  0xc4; 0x43; 0x3d; 0x02; 0xe0; 0xaa;
                           (* VPBLENDD (%_% ymm12) (%_% ymm8) (%_% ymm8) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x35; 0xfa; 0xc4;
                           (* VPSUBD (%_% ymm8) (%_% ymm9) (%_% ymm12) *)
  0xc4; 0x41; 0x35; 0xfe; 0xc1;
                           (* VPADDD (%_% ymm8) (%_% ymm9) (%_% ymm9) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xf5; 0xaa;
                           (* VPBLENDD (%_% ymm14) (%_% ymm13) (%_% ymm13) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x1d; 0xfe; 0xe8;
                           (* VPADDD (%_% ymm13) (%_% ymm12) (%_% ymm8) *)
  0xc4; 0x41; 0x35; 0xfa; 0xe9;
                           (* VPSUBD (%_% ymm13) (%_% ymm9) (%_% ymm9) *)
  0xc5; 0xfd; 0x6f; 0x8e; 0xe0; 0x03; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm1) (Memop Word256 (%% (rsi,992))) *)
  0xc5; 0xfd; 0x6f; 0x96; 0x80; 0x08; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm2) (Memop Word256 (%% (rsi,2176))) *)
  0xc4; 0xc1; 0x75; 0x73; 0xd2; 0x20;
                           (* VPSRLQ (%_% ymm1) (%_% ymm10) (Imm8 (word 32)) *)
  0xc4; 0xc1; 0x7e; 0x16; 0xd7;
                           (* VMOVSHDUP (%_% ymm2) (%_% ymm15) *)
  0xc4; 0xc2; 0x4d; 0x28; 0xcd;
                           (* VPMULDQ (%_% ymm1) (%_% ymm6) (%_% ymm13) *)
  0xc4; 0xc1; 0x7e; 0x16; 0xf4;
                           (* VMOVSHDUP (%_% ymm6) (%_% ymm12) *)
  0xc4; 0x42; 0x1d; 0x28; 0xd6;
                           (* VPMULDQ (%_% ymm10) (%_% ymm12) (%_% ymm14) *)
  0xc4; 0xe2; 0x4d; 0x28; 0xd6;
                           (* VPMULDQ (%_% ymm2) (%_% ymm6) (%_% ymm6) *)
  0xc4; 0x42; 0x1d; 0x28; 0xfc;
                           (* VPMULDQ (%_% ymm15) (%_% ymm12) (%_% ymm12) *)
  0xc4; 0xc2; 0x15; 0x28; 0xc5;
                           (* VPMULDQ (%_% ymm0) (%_% ymm13) (%_% ymm13) *)
  0xc4; 0xc2; 0x0d; 0x28; 0xc6;
                           (* VPMULDQ (%_% ymm0) (%_% ymm14) (%_% ymm14) *)
  0xc5; 0xfe; 0x16; 0xf6;  (* VMOVSHDUP (%_% ymm6) (%_% ymm6) *)
  0xc4; 0x63; 0x4d; 0x02; 0xe6; 0xaa;
                           (* VPBLENDD (%_% ymm12) (%_% ymm6) (%_% ymm6) (Imm8 (word 170)) *)
  0xc4; 0xc1; 0x45; 0xfa; 0xf4;
                           (* VPSUBD (%_% ymm6) (%_% ymm7) (%_% ymm12) *)
  0xc5; 0xc5; 0xfe; 0xf7;  (* VPADDD (%_% ymm6) (%_% ymm7) (%_% ymm7) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xf5; 0xaa;
                           (* VPBLENDD (%_% ymm14) (%_% ymm13) (%_% ymm13) (Imm8 (word 170)) *)
  0xc5; 0x1d; 0xfe; 0xee;  (* VPADDD (%_% ymm13) (%_% ymm12) (%_% ymm6) *)
  0xc5; 0x45; 0xfa; 0xef;  (* VPSUBD (%_% ymm13) (%_% ymm7) (%_% ymm7) *)
  0xc5; 0xfd; 0x6f; 0x8e; 0x60; 0x04; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm1) (Memop Word256 (%% (rsi,1120))) *)
  0xc5; 0xfd; 0x6f; 0x96; 0x00; 0x09; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm2) (Memop Word256 (%% (rsi,2304))) *)
  0xc4; 0xc1; 0x75; 0x73; 0xd2; 0x20;
                           (* VPSRLQ (%_% ymm1) (%_% ymm10) (Imm8 (word 32)) *)
  0xc4; 0xc1; 0x7e; 0x16; 0xd7;
                           (* VMOVSHDUP (%_% ymm2) (%_% ymm15) *)
  0xc4; 0xc2; 0x5d; 0x28; 0xcd;
                           (* VPMULDQ (%_% ymm1) (%_% ymm4) (%_% ymm13) *)
  0xc4; 0xc1; 0x7e; 0x16; 0xe4;
                           (* VMOVSHDUP (%_% ymm4) (%_% ymm12) *)
  0xc4; 0x42; 0x1d; 0x28; 0xd6;
                           (* VPMULDQ (%_% ymm10) (%_% ymm12) (%_% ymm14) *)
  0xc4; 0xe2; 0x5d; 0x28; 0xd4;
                           (* VPMULDQ (%_% ymm2) (%_% ymm4) (%_% ymm4) *)
  0xc4; 0x42; 0x1d; 0x28; 0xfc;
                           (* VPMULDQ (%_% ymm15) (%_% ymm12) (%_% ymm12) *)
  0xc4; 0xc2; 0x15; 0x28; 0xc5;
                           (* VPMULDQ (%_% ymm0) (%_% ymm13) (%_% ymm13) *)
  0xc4; 0xc2; 0x0d; 0x28; 0xc6;
                           (* VPMULDQ (%_% ymm0) (%_% ymm14) (%_% ymm14) *)
  0xc5; 0xfe; 0x16; 0xe4;  (* VMOVSHDUP (%_% ymm4) (%_% ymm4) *)
  0xc4; 0x63; 0x5d; 0x02; 0xe4; 0xaa;
                           (* VPBLENDD (%_% ymm12) (%_% ymm4) (%_% ymm4) (Imm8 (word 170)) *)
  0xc4; 0xc1; 0x55; 0xfa; 0xe4;
                           (* VPSUBD (%_% ymm4) (%_% ymm5) (%_% ymm12) *)
  0xc5; 0xd5; 0xfe; 0xe5;  (* VPADDD (%_% ymm4) (%_% ymm5) (%_% ymm5) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xf5; 0xaa;
                           (* VPBLENDD (%_% ymm14) (%_% ymm13) (%_% ymm13) (Imm8 (word 170)) *)
  0xc5; 0x1d; 0xfe; 0xec;  (* VPADDD (%_% ymm13) (%_% ymm12) (%_% ymm4) *)
  0xc5; 0x55; 0xfa; 0xed;  (* VPSUBD (%_% ymm13) (%_% ymm5) (%_% ymm5) *)
  0xc5; 0xfd; 0x6f; 0x8e; 0xe0; 0x04; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm1) (Memop Word256 (%% (rsi,1248))) *)
  0xc5; 0xfd; 0x6f; 0x96; 0x80; 0x09; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm2) (Memop Word256 (%% (rsi,2432))) *)
  0xc4; 0xc1; 0x75; 0x73; 0xd2; 0x20;
                           (* VPSRLQ (%_% ymm1) (%_% ymm10) (Imm8 (word 32)) *)
  0xc4; 0xc1; 0x7e; 0x16; 0xd7;
                           (* VMOVSHDUP (%_% ymm2) (%_% ymm15) *)
  0xc4; 0xc2; 0x25; 0x28; 0xcd;
                           (* VPMULDQ (%_% ymm1) (%_% ymm11) (%_% ymm13) *)
  0xc4; 0x41; 0x7e; 0x16; 0xdc;
                           (* VMOVSHDUP (%_% ymm11) (%_% ymm12) *)
  0xc4; 0x42; 0x1d; 0x28; 0xd6;
                           (* VPMULDQ (%_% ymm10) (%_% ymm12) (%_% ymm14) *)
  0xc4; 0xc2; 0x25; 0x28; 0xd3;
                           (* VPMULDQ (%_% ymm2) (%_% ymm11) (%_% ymm11) *)
  0xc4; 0x42; 0x1d; 0x28; 0xfc;
                           (* VPMULDQ (%_% ymm15) (%_% ymm12) (%_% ymm12) *)
  0xc4; 0xc2; 0x15; 0x28; 0xc5;
                           (* VPMULDQ (%_% ymm0) (%_% ymm13) (%_% ymm13) *)
  0xc4; 0xc2; 0x0d; 0x28; 0xc6;
                           (* VPMULDQ (%_% ymm0) (%_% ymm14) (%_% ymm14) *)
  0xc4; 0x41; 0x7e; 0x16; 0xdb;
                           (* VMOVSHDUP (%_% ymm11) (%_% ymm11) *)
  0xc4; 0x43; 0x25; 0x02; 0xe3; 0xaa;
                           (* VPBLENDD (%_% ymm12) (%_% ymm11) (%_% ymm11) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x65; 0xfa; 0xdc;
                           (* VPSUBD (%_% ymm11) (%_% ymm3) (%_% ymm12) *)
  0xc5; 0x65; 0xfe; 0xdb;  (* VPADDD (%_% ymm11) (%_% ymm3) (%_% ymm3) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xf5; 0xaa;
                           (* VPBLENDD (%_% ymm14) (%_% ymm13) (%_% ymm13) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x1d; 0xfe; 0xeb;
                           (* VPADDD (%_% ymm13) (%_% ymm12) (%_% ymm11) *)
  0xc5; 0x65; 0xfa; 0xeb;  (* VPSUBD (%_% ymm13) (%_% ymm3) (%_% ymm3) *)
  0xc5; 0x7d; 0x7f; 0x8f; 0x00; 0x02; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,512))) (%_% ymm9) *)
  0xc5; 0x7d; 0x7f; 0x87; 0x20; 0x02; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,544))) (%_% ymm8) *)
  0xc5; 0xfd; 0x7f; 0xbf; 0x40; 0x02; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,576))) (%_% ymm7) *)
  0xc5; 0xfd; 0x7f; 0xb7; 0x60; 0x02; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,608))) (%_% ymm6) *)
  0xc5; 0xfd; 0x7f; 0xaf; 0x80; 0x02; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,640))) (%_% ymm5) *)
  0xc5; 0xfd; 0x7f; 0xa7; 0xa0; 0x02; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,672))) (%_% ymm4) *)
  0xc5; 0xfd; 0x7f; 0x9f; 0xc0; 0x02; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,704))) (%_% ymm3) *)
  0xc5; 0x7d; 0x7f; 0x9f; 0xe0; 0x02; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,736))) (%_% ymm11) *)
  0xc5; 0xfd; 0x6f; 0xa7; 0x00; 0x03; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm4) (Memop Word256 (%% (rdi,768))) *)
  0xc5; 0xfd; 0x6f; 0xaf; 0x20; 0x03; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm5) (Memop Word256 (%% (rdi,800))) *)
  0xc5; 0xfd; 0x6f; 0xb7; 0x40; 0x03; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm6) (Memop Word256 (%% (rdi,832))) *)
  0xc5; 0xfd; 0x6f; 0xbf; 0x60; 0x03; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm7) (Memop Word256 (%% (rdi,864))) *)
  0xc5; 0x7d; 0x6f; 0x87; 0x80; 0x03; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm8) (Memop Word256 (%% (rdi,896))) *)
  0xc5; 0x7d; 0x6f; 0x8f; 0xa0; 0x03; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm9) (Memop Word256 (%% (rdi,928))) *)
  0xc5; 0x7d; 0x6f; 0x97; 0xc0; 0x03; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm10) (Memop Word256 (%% (rdi,960))) *)
  0xc5; 0x7d; 0x6f; 0x9f; 0xe0; 0x03; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm11) (Memop Word256 (%% (rdi,992))) *)
  0xc4; 0xe2; 0x7d; 0x58; 0x8e; 0x9c; 0x00; 0x00; 0x00;
                           (* VPBROADCASTD (%_% ymm1) (Memop Word128 (%% (rsi,156))) *)
  0xc4; 0xe2; 0x7d; 0x58; 0x96; 0x3c; 0x05; 0x00; 0x00;
                           (* VPBROADCASTD (%_% ymm2) (Memop Word128 (%% (rsi,1340))) *)
  0xc4; 0xc2; 0x3d; 0x28; 0xcd;
                           (* VPMULDQ (%_% ymm1) (%_% ymm8) (%_% ymm13) *)
  0xc4; 0x41; 0x7e; 0x16; 0xc4;
                           (* VMOVSHDUP (%_% ymm8) (%_% ymm12) *)
  0xc4; 0xc2; 0x1d; 0x28; 0xce;
                           (* VPMULDQ (%_% ymm1) (%_% ymm12) (%_% ymm14) *)
  0xc4; 0xc2; 0x3d; 0x28; 0xd0;
                           (* VPMULDQ (%_% ymm2) (%_% ymm8) (%_% ymm8) *)
  0xc4; 0xc2; 0x1d; 0x28; 0xd4;
                           (* VPMULDQ (%_% ymm2) (%_% ymm12) (%_% ymm12) *)
  0xc4; 0xc2; 0x15; 0x28; 0xc5;
                           (* VPMULDQ (%_% ymm0) (%_% ymm13) (%_% ymm13) *)
  0xc4; 0xc2; 0x0d; 0x28; 0xc6;
                           (* VPMULDQ (%_% ymm0) (%_% ymm14) (%_% ymm14) *)
  0xc4; 0x41; 0x7e; 0x16; 0xc0;
                           (* VMOVSHDUP (%_% ymm8) (%_% ymm8) *)
  0xc4; 0x43; 0x3d; 0x02; 0xe0; 0xaa;
                           (* VPBLENDD (%_% ymm12) (%_% ymm8) (%_% ymm8) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x5d; 0xfa; 0xc4;
                           (* VPSUBD (%_% ymm8) (%_% ymm4) (%_% ymm12) *)
  0xc5; 0x5d; 0xfe; 0xc4;  (* VPADDD (%_% ymm8) (%_% ymm4) (%_% ymm4) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xf5; 0xaa;
                           (* VPBLENDD (%_% ymm14) (%_% ymm13) (%_% ymm13) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x1d; 0xfe; 0xe8;
                           (* VPADDD (%_% ymm13) (%_% ymm12) (%_% ymm8) *)
  0xc5; 0x5d; 0xfa; 0xec;  (* VPSUBD (%_% ymm13) (%_% ymm4) (%_% ymm4) *)
  0xc4; 0xc2; 0x35; 0x28; 0xcd;
                           (* VPMULDQ (%_% ymm1) (%_% ymm9) (%_% ymm13) *)
  0xc4; 0x41; 0x7e; 0x16; 0xcc;
                           (* VMOVSHDUP (%_% ymm9) (%_% ymm12) *)
  0xc4; 0xc2; 0x1d; 0x28; 0xce;
                           (* VPMULDQ (%_% ymm1) (%_% ymm12) (%_% ymm14) *)
  0xc4; 0xc2; 0x35; 0x28; 0xd1;
                           (* VPMULDQ (%_% ymm2) (%_% ymm9) (%_% ymm9) *)
  0xc4; 0xc2; 0x1d; 0x28; 0xd4;
                           (* VPMULDQ (%_% ymm2) (%_% ymm12) (%_% ymm12) *)
  0xc4; 0xc2; 0x15; 0x28; 0xc5;
                           (* VPMULDQ (%_% ymm0) (%_% ymm13) (%_% ymm13) *)
  0xc4; 0xc2; 0x0d; 0x28; 0xc6;
                           (* VPMULDQ (%_% ymm0) (%_% ymm14) (%_% ymm14) *)
  0xc4; 0x41; 0x7e; 0x16; 0xc9;
                           (* VMOVSHDUP (%_% ymm9) (%_% ymm9) *)
  0xc4; 0x43; 0x35; 0x02; 0xe1; 0xaa;
                           (* VPBLENDD (%_% ymm12) (%_% ymm9) (%_% ymm9) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x55; 0xfa; 0xcc;
                           (* VPSUBD (%_% ymm9) (%_% ymm5) (%_% ymm12) *)
  0xc5; 0x55; 0xfe; 0xcd;  (* VPADDD (%_% ymm9) (%_% ymm5) (%_% ymm5) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xf5; 0xaa;
                           (* VPBLENDD (%_% ymm14) (%_% ymm13) (%_% ymm13) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x1d; 0xfe; 0xe9;
                           (* VPADDD (%_% ymm13) (%_% ymm12) (%_% ymm9) *)
  0xc5; 0x55; 0xfa; 0xed;  (* VPSUBD (%_% ymm13) (%_% ymm5) (%_% ymm5) *)
  0xc4; 0xc2; 0x2d; 0x28; 0xcd;
                           (* VPMULDQ (%_% ymm1) (%_% ymm10) (%_% ymm13) *)
  0xc4; 0x41; 0x7e; 0x16; 0xd4;
                           (* VMOVSHDUP (%_% ymm10) (%_% ymm12) *)
  0xc4; 0xc2; 0x1d; 0x28; 0xce;
                           (* VPMULDQ (%_% ymm1) (%_% ymm12) (%_% ymm14) *)
  0xc4; 0xc2; 0x2d; 0x28; 0xd2;
                           (* VPMULDQ (%_% ymm2) (%_% ymm10) (%_% ymm10) *)
  0xc4; 0xc2; 0x1d; 0x28; 0xd4;
                           (* VPMULDQ (%_% ymm2) (%_% ymm12) (%_% ymm12) *)
  0xc4; 0xc2; 0x15; 0x28; 0xc5;
                           (* VPMULDQ (%_% ymm0) (%_% ymm13) (%_% ymm13) *)
  0xc4; 0xc2; 0x0d; 0x28; 0xc6;
                           (* VPMULDQ (%_% ymm0) (%_% ymm14) (%_% ymm14) *)
  0xc4; 0x41; 0x7e; 0x16; 0xd2;
                           (* VMOVSHDUP (%_% ymm10) (%_% ymm10) *)
  0xc4; 0x43; 0x2d; 0x02; 0xe2; 0xaa;
                           (* VPBLENDD (%_% ymm12) (%_% ymm10) (%_% ymm10) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x4d; 0xfa; 0xd4;
                           (* VPSUBD (%_% ymm10) (%_% ymm6) (%_% ymm12) *)
  0xc5; 0x4d; 0xfe; 0xd6;  (* VPADDD (%_% ymm10) (%_% ymm6) (%_% ymm6) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xf5; 0xaa;
                           (* VPBLENDD (%_% ymm14) (%_% ymm13) (%_% ymm13) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x1d; 0xfe; 0xea;
                           (* VPADDD (%_% ymm13) (%_% ymm12) (%_% ymm10) *)
  0xc5; 0x4d; 0xfa; 0xee;  (* VPSUBD (%_% ymm13) (%_% ymm6) (%_% ymm6) *)
  0xc4; 0xc2; 0x25; 0x28; 0xcd;
                           (* VPMULDQ (%_% ymm1) (%_% ymm11) (%_% ymm13) *)
  0xc4; 0x41; 0x7e; 0x16; 0xdc;
                           (* VMOVSHDUP (%_% ymm11) (%_% ymm12) *)
  0xc4; 0xc2; 0x1d; 0x28; 0xce;
                           (* VPMULDQ (%_% ymm1) (%_% ymm12) (%_% ymm14) *)
  0xc4; 0xc2; 0x25; 0x28; 0xd3;
                           (* VPMULDQ (%_% ymm2) (%_% ymm11) (%_% ymm11) *)
  0xc4; 0xc2; 0x1d; 0x28; 0xd4;
                           (* VPMULDQ (%_% ymm2) (%_% ymm12) (%_% ymm12) *)
  0xc4; 0xc2; 0x15; 0x28; 0xc5;
                           (* VPMULDQ (%_% ymm0) (%_% ymm13) (%_% ymm13) *)
  0xc4; 0xc2; 0x0d; 0x28; 0xc6;
                           (* VPMULDQ (%_% ymm0) (%_% ymm14) (%_% ymm14) *)
  0xc4; 0x41; 0x7e; 0x16; 0xdb;
                           (* VMOVSHDUP (%_% ymm11) (%_% ymm11) *)
  0xc4; 0x43; 0x25; 0x02; 0xe3; 0xaa;
                           (* VPBLENDD (%_% ymm12) (%_% ymm11) (%_% ymm11) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x45; 0xfa; 0xdc;
                           (* VPSUBD (%_% ymm11) (%_% ymm7) (%_% ymm12) *)
  0xc5; 0x45; 0xfe; 0xdf;  (* VPADDD (%_% ymm11) (%_% ymm7) (%_% ymm7) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xf5; 0xaa;
                           (* VPBLENDD (%_% ymm14) (%_% ymm13) (%_% ymm13) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x1d; 0xfe; 0xeb;
                           (* VPADDD (%_% ymm13) (%_% ymm12) (%_% ymm11) *)
  0xc5; 0x45; 0xfa; 0xef;  (* VPSUBD (%_% ymm13) (%_% ymm7) (%_% ymm7) *)
  0xc4; 0xc3; 0x5d; 0x46; 0xd8; 0x20;
                           (* VPERM2I128 (%_% ymm3) (%_% ymm4) (%_% ymm8) (Imm8 (word 32)) *)
  0xc4; 0x43; 0x5d; 0x46; 0xc0; 0x31;
                           (* VPERM2I128 (%_% ymm8) (%_% ymm4) (%_% ymm8) (Imm8 (word 49)) *)
  0xc4; 0xc3; 0x55; 0x46; 0xe1; 0x20;
                           (* VPERM2I128 (%_% ymm4) (%_% ymm5) (%_% ymm9) (Imm8 (word 32)) *)
  0xc4; 0x43; 0x55; 0x46; 0xc9; 0x31;
                           (* VPERM2I128 (%_% ymm9) (%_% ymm5) (%_% ymm9) (Imm8 (word 49)) *)
  0xc4; 0xc3; 0x4d; 0x46; 0xea; 0x20;
                           (* VPERM2I128 (%_% ymm5) (%_% ymm6) (%_% ymm10) (Imm8 (word 32)) *)
  0xc4; 0x43; 0x4d; 0x46; 0xd2; 0x31;
                           (* VPERM2I128 (%_% ymm10) (%_% ymm6) (%_% ymm10) (Imm8 (word 49)) *)
  0xc4; 0xc3; 0x45; 0x46; 0xf3; 0x20;
                           (* VPERM2I128 (%_% ymm6) (%_% ymm7) (%_% ymm11) (Imm8 (word 32)) *)
  0xc4; 0x43; 0x45; 0x46; 0xdb; 0x31;
                           (* VPERM2I128 (%_% ymm11) (%_% ymm7) (%_% ymm11) (Imm8 (word 49)) *)
  0xc5; 0xfd; 0x6f; 0x8e; 0x00; 0x01; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm1) (Memop Word256 (%% (rsi,256))) *)
  0xc5; 0xfd; 0x6f; 0x96; 0xa0; 0x05; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm2) (Memop Word256 (%% (rsi,1440))) *)
  0xc4; 0xc2; 0x55; 0x28; 0xcd;
                           (* VPMULDQ (%_% ymm1) (%_% ymm5) (%_% ymm13) *)
  0xc4; 0xc1; 0x7e; 0x16; 0xec;
                           (* VMOVSHDUP (%_% ymm5) (%_% ymm12) *)
  0xc4; 0xc2; 0x1d; 0x28; 0xce;
                           (* VPMULDQ (%_% ymm1) (%_% ymm12) (%_% ymm14) *)
  0xc4; 0xe2; 0x55; 0x28; 0xd5;
                           (* VPMULDQ (%_% ymm2) (%_% ymm5) (%_% ymm5) *)
  0xc4; 0xc2; 0x1d; 0x28; 0xd4;
                           (* VPMULDQ (%_% ymm2) (%_% ymm12) (%_% ymm12) *)
  0xc4; 0xc2; 0x15; 0x28; 0xc5;
                           (* VPMULDQ (%_% ymm0) (%_% ymm13) (%_% ymm13) *)
  0xc4; 0xc2; 0x0d; 0x28; 0xc6;
                           (* VPMULDQ (%_% ymm0) (%_% ymm14) (%_% ymm14) *)
  0xc5; 0xfe; 0x16; 0xed;  (* VMOVSHDUP (%_% ymm5) (%_% ymm5) *)
  0xc4; 0x63; 0x55; 0x02; 0xe5; 0xaa;
                           (* VPBLENDD (%_% ymm12) (%_% ymm5) (%_% ymm5) (Imm8 (word 170)) *)
  0xc4; 0xc1; 0x65; 0xfa; 0xec;
                           (* VPSUBD (%_% ymm5) (%_% ymm3) (%_% ymm12) *)
  0xc5; 0xe5; 0xfe; 0xeb;  (* VPADDD (%_% ymm5) (%_% ymm3) (%_% ymm3) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xf5; 0xaa;
                           (* VPBLENDD (%_% ymm14) (%_% ymm13) (%_% ymm13) (Imm8 (word 170)) *)
  0xc5; 0x1d; 0xfe; 0xed;  (* VPADDD (%_% ymm13) (%_% ymm12) (%_% ymm5) *)
  0xc5; 0x65; 0xfa; 0xeb;  (* VPSUBD (%_% ymm13) (%_% ymm3) (%_% ymm3) *)
  0xc4; 0xc2; 0x2d; 0x28; 0xcd;
                           (* VPMULDQ (%_% ymm1) (%_% ymm10) (%_% ymm13) *)
  0xc4; 0x41; 0x7e; 0x16; 0xd4;
                           (* VMOVSHDUP (%_% ymm10) (%_% ymm12) *)
  0xc4; 0xc2; 0x1d; 0x28; 0xce;
                           (* VPMULDQ (%_% ymm1) (%_% ymm12) (%_% ymm14) *)
  0xc4; 0xc2; 0x2d; 0x28; 0xd2;
                           (* VPMULDQ (%_% ymm2) (%_% ymm10) (%_% ymm10) *)
  0xc4; 0xc2; 0x1d; 0x28; 0xd4;
                           (* VPMULDQ (%_% ymm2) (%_% ymm12) (%_% ymm12) *)
  0xc4; 0xc2; 0x15; 0x28; 0xc5;
                           (* VPMULDQ (%_% ymm0) (%_% ymm13) (%_% ymm13) *)
  0xc4; 0xc2; 0x0d; 0x28; 0xc6;
                           (* VPMULDQ (%_% ymm0) (%_% ymm14) (%_% ymm14) *)
  0xc4; 0x41; 0x7e; 0x16; 0xd2;
                           (* VMOVSHDUP (%_% ymm10) (%_% ymm10) *)
  0xc4; 0x43; 0x2d; 0x02; 0xe2; 0xaa;
                           (* VPBLENDD (%_% ymm12) (%_% ymm10) (%_% ymm10) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x3d; 0xfa; 0xd4;
                           (* VPSUBD (%_% ymm10) (%_% ymm8) (%_% ymm12) *)
  0xc4; 0x41; 0x3d; 0xfe; 0xd0;
                           (* VPADDD (%_% ymm10) (%_% ymm8) (%_% ymm8) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xf5; 0xaa;
                           (* VPBLENDD (%_% ymm14) (%_% ymm13) (%_% ymm13) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x1d; 0xfe; 0xea;
                           (* VPADDD (%_% ymm13) (%_% ymm12) (%_% ymm10) *)
  0xc4; 0x41; 0x3d; 0xfa; 0xe8;
                           (* VPSUBD (%_% ymm13) (%_% ymm8) (%_% ymm8) *)
  0xc4; 0xc2; 0x4d; 0x28; 0xcd;
                           (* VPMULDQ (%_% ymm1) (%_% ymm6) (%_% ymm13) *)
  0xc4; 0xc1; 0x7e; 0x16; 0xf4;
                           (* VMOVSHDUP (%_% ymm6) (%_% ymm12) *)
  0xc4; 0xc2; 0x1d; 0x28; 0xce;
                           (* VPMULDQ (%_% ymm1) (%_% ymm12) (%_% ymm14) *)
  0xc4; 0xe2; 0x4d; 0x28; 0xd6;
                           (* VPMULDQ (%_% ymm2) (%_% ymm6) (%_% ymm6) *)
  0xc4; 0xc2; 0x1d; 0x28; 0xd4;
                           (* VPMULDQ (%_% ymm2) (%_% ymm12) (%_% ymm12) *)
  0xc4; 0xc2; 0x15; 0x28; 0xc5;
                           (* VPMULDQ (%_% ymm0) (%_% ymm13) (%_% ymm13) *)
  0xc4; 0xc2; 0x0d; 0x28; 0xc6;
                           (* VPMULDQ (%_% ymm0) (%_% ymm14) (%_% ymm14) *)
  0xc5; 0xfe; 0x16; 0xf6;  (* VMOVSHDUP (%_% ymm6) (%_% ymm6) *)
  0xc4; 0x63; 0x4d; 0x02; 0xe6; 0xaa;
                           (* VPBLENDD (%_% ymm12) (%_% ymm6) (%_% ymm6) (Imm8 (word 170)) *)
  0xc4; 0xc1; 0x5d; 0xfa; 0xf4;
                           (* VPSUBD (%_% ymm6) (%_% ymm4) (%_% ymm12) *)
  0xc5; 0xdd; 0xfe; 0xf4;  (* VPADDD (%_% ymm6) (%_% ymm4) (%_% ymm4) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xf5; 0xaa;
                           (* VPBLENDD (%_% ymm14) (%_% ymm13) (%_% ymm13) (Imm8 (word 170)) *)
  0xc5; 0x1d; 0xfe; 0xee;  (* VPADDD (%_% ymm13) (%_% ymm12) (%_% ymm6) *)
  0xc5; 0x5d; 0xfa; 0xec;  (* VPSUBD (%_% ymm13) (%_% ymm4) (%_% ymm4) *)
  0xc4; 0xc2; 0x25; 0x28; 0xcd;
                           (* VPMULDQ (%_% ymm1) (%_% ymm11) (%_% ymm13) *)
  0xc4; 0x41; 0x7e; 0x16; 0xdc;
                           (* VMOVSHDUP (%_% ymm11) (%_% ymm12) *)
  0xc4; 0xc2; 0x1d; 0x28; 0xce;
                           (* VPMULDQ (%_% ymm1) (%_% ymm12) (%_% ymm14) *)
  0xc4; 0xc2; 0x25; 0x28; 0xd3;
                           (* VPMULDQ (%_% ymm2) (%_% ymm11) (%_% ymm11) *)
  0xc4; 0xc2; 0x1d; 0x28; 0xd4;
                           (* VPMULDQ (%_% ymm2) (%_% ymm12) (%_% ymm12) *)
  0xc4; 0xc2; 0x15; 0x28; 0xc5;
                           (* VPMULDQ (%_% ymm0) (%_% ymm13) (%_% ymm13) *)
  0xc4; 0xc2; 0x0d; 0x28; 0xc6;
                           (* VPMULDQ (%_% ymm0) (%_% ymm14) (%_% ymm14) *)
  0xc4; 0x41; 0x7e; 0x16; 0xdb;
                           (* VMOVSHDUP (%_% ymm11) (%_% ymm11) *)
  0xc4; 0x43; 0x25; 0x02; 0xe3; 0xaa;
                           (* VPBLENDD (%_% ymm12) (%_% ymm11) (%_% ymm11) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x35; 0xfa; 0xdc;
                           (* VPSUBD (%_% ymm11) (%_% ymm9) (%_% ymm12) *)
  0xc4; 0x41; 0x35; 0xfe; 0xd9;
                           (* VPADDD (%_% ymm11) (%_% ymm9) (%_% ymm9) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xf5; 0xaa;
                           (* VPBLENDD (%_% ymm14) (%_% ymm13) (%_% ymm13) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x1d; 0xfe; 0xeb;
                           (* VPADDD (%_% ymm13) (%_% ymm12) (%_% ymm11) *)
  0xc4; 0x41; 0x35; 0xfa; 0xe9;
                           (* VPSUBD (%_% ymm13) (%_% ymm9) (%_% ymm9) *)
  0xc5; 0xe5; 0x6c; 0xfd;  (* VPUNPCKLQDQ (%_% ymm7) (%_% ymm3) (%_% ymm5) *)
  0xc5; 0xe5; 0x6d; 0xed;  (* VPUNPCKHQDQ (%_% ymm5) (%_% ymm3) (%_% ymm5) *)
  0xc4; 0xc1; 0x3d; 0x6c; 0xda;
                           (* VPUNPCKLQDQ (%_% ymm3) (%_% ymm8) (%_% ymm10) *)
  0xc4; 0x41; 0x3d; 0x6d; 0xd2;
                           (* VPUNPCKHQDQ (%_% ymm10) (%_% ymm8) (%_% ymm10) *)
  0xc5; 0x5d; 0x6c; 0xc6;  (* VPUNPCKLQDQ (%_% ymm8) (%_% ymm4) (%_% ymm6) *)
  0xc5; 0xdd; 0x6d; 0xf6;  (* VPUNPCKHQDQ (%_% ymm6) (%_% ymm4) (%_% ymm6) *)
  0xc4; 0xc1; 0x35; 0x6c; 0xe3;
                           (* VPUNPCKLQDQ (%_% ymm4) (%_% ymm9) (%_% ymm11) *)
  0xc4; 0x41; 0x35; 0x6d; 0xdb;
                           (* VPUNPCKHQDQ (%_% ymm11) (%_% ymm9) (%_% ymm11) *)
  0xc5; 0xfd; 0x6f; 0x8e; 0x80; 0x01; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm1) (Memop Word256 (%% (rsi,384))) *)
  0xc5; 0xfd; 0x6f; 0x96; 0x20; 0x06; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm2) (Memop Word256 (%% (rsi,1568))) *)
  0xc4; 0xc2; 0x3d; 0x28; 0xcd;
                           (* VPMULDQ (%_% ymm1) (%_% ymm8) (%_% ymm13) *)
  0xc4; 0x41; 0x7e; 0x16; 0xc4;
                           (* VMOVSHDUP (%_% ymm8) (%_% ymm12) *)
  0xc4; 0xc2; 0x1d; 0x28; 0xce;
                           (* VPMULDQ (%_% ymm1) (%_% ymm12) (%_% ymm14) *)
  0xc4; 0xc2; 0x3d; 0x28; 0xd0;
                           (* VPMULDQ (%_% ymm2) (%_% ymm8) (%_% ymm8) *)
  0xc4; 0xc2; 0x1d; 0x28; 0xd4;
                           (* VPMULDQ (%_% ymm2) (%_% ymm12) (%_% ymm12) *)
  0xc4; 0xc2; 0x15; 0x28; 0xc5;
                           (* VPMULDQ (%_% ymm0) (%_% ymm13) (%_% ymm13) *)
  0xc4; 0xc2; 0x0d; 0x28; 0xc6;
                           (* VPMULDQ (%_% ymm0) (%_% ymm14) (%_% ymm14) *)
  0xc4; 0x41; 0x7e; 0x16; 0xc0;
                           (* VMOVSHDUP (%_% ymm8) (%_% ymm8) *)
  0xc4; 0x43; 0x3d; 0x02; 0xe0; 0xaa;
                           (* VPBLENDD (%_% ymm12) (%_% ymm8) (%_% ymm8) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x45; 0xfa; 0xc4;
                           (* VPSUBD (%_% ymm8) (%_% ymm7) (%_% ymm12) *)
  0xc5; 0x45; 0xfe; 0xc7;  (* VPADDD (%_% ymm8) (%_% ymm7) (%_% ymm7) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xf5; 0xaa;
                           (* VPBLENDD (%_% ymm14) (%_% ymm13) (%_% ymm13) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x1d; 0xfe; 0xe8;
                           (* VPADDD (%_% ymm13) (%_% ymm12) (%_% ymm8) *)
  0xc5; 0x45; 0xfa; 0xef;  (* VPSUBD (%_% ymm13) (%_% ymm7) (%_% ymm7) *)
  0xc4; 0xc2; 0x4d; 0x28; 0xcd;
                           (* VPMULDQ (%_% ymm1) (%_% ymm6) (%_% ymm13) *)
  0xc4; 0xc1; 0x7e; 0x16; 0xf4;
                           (* VMOVSHDUP (%_% ymm6) (%_% ymm12) *)
  0xc4; 0xc2; 0x1d; 0x28; 0xce;
                           (* VPMULDQ (%_% ymm1) (%_% ymm12) (%_% ymm14) *)
  0xc4; 0xe2; 0x4d; 0x28; 0xd6;
                           (* VPMULDQ (%_% ymm2) (%_% ymm6) (%_% ymm6) *)
  0xc4; 0xc2; 0x1d; 0x28; 0xd4;
                           (* VPMULDQ (%_% ymm2) (%_% ymm12) (%_% ymm12) *)
  0xc4; 0xc2; 0x15; 0x28; 0xc5;
                           (* VPMULDQ (%_% ymm0) (%_% ymm13) (%_% ymm13) *)
  0xc4; 0xc2; 0x0d; 0x28; 0xc6;
                           (* VPMULDQ (%_% ymm0) (%_% ymm14) (%_% ymm14) *)
  0xc5; 0xfe; 0x16; 0xf6;  (* VMOVSHDUP (%_% ymm6) (%_% ymm6) *)
  0xc4; 0x63; 0x4d; 0x02; 0xe6; 0xaa;
                           (* VPBLENDD (%_% ymm12) (%_% ymm6) (%_% ymm6) (Imm8 (word 170)) *)
  0xc4; 0xc1; 0x55; 0xfa; 0xf4;
                           (* VPSUBD (%_% ymm6) (%_% ymm5) (%_% ymm12) *)
  0xc5; 0xd5; 0xfe; 0xf5;  (* VPADDD (%_% ymm6) (%_% ymm5) (%_% ymm5) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xf5; 0xaa;
                           (* VPBLENDD (%_% ymm14) (%_% ymm13) (%_% ymm13) (Imm8 (word 170)) *)
  0xc5; 0x1d; 0xfe; 0xee;  (* VPADDD (%_% ymm13) (%_% ymm12) (%_% ymm6) *)
  0xc5; 0x55; 0xfa; 0xed;  (* VPSUBD (%_% ymm13) (%_% ymm5) (%_% ymm5) *)
  0xc4; 0xc2; 0x5d; 0x28; 0xcd;
                           (* VPMULDQ (%_% ymm1) (%_% ymm4) (%_% ymm13) *)
  0xc4; 0xc1; 0x7e; 0x16; 0xe4;
                           (* VMOVSHDUP (%_% ymm4) (%_% ymm12) *)
  0xc4; 0xc2; 0x1d; 0x28; 0xce;
                           (* VPMULDQ (%_% ymm1) (%_% ymm12) (%_% ymm14) *)
  0xc4; 0xe2; 0x5d; 0x28; 0xd4;
                           (* VPMULDQ (%_% ymm2) (%_% ymm4) (%_% ymm4) *)
  0xc4; 0xc2; 0x1d; 0x28; 0xd4;
                           (* VPMULDQ (%_% ymm2) (%_% ymm12) (%_% ymm12) *)
  0xc4; 0xc2; 0x15; 0x28; 0xc5;
                           (* VPMULDQ (%_% ymm0) (%_% ymm13) (%_% ymm13) *)
  0xc4; 0xc2; 0x0d; 0x28; 0xc6;
                           (* VPMULDQ (%_% ymm0) (%_% ymm14) (%_% ymm14) *)
  0xc5; 0xfe; 0x16; 0xe4;  (* VMOVSHDUP (%_% ymm4) (%_% ymm4) *)
  0xc4; 0x63; 0x5d; 0x02; 0xe4; 0xaa;
                           (* VPBLENDD (%_% ymm12) (%_% ymm4) (%_% ymm4) (Imm8 (word 170)) *)
  0xc4; 0xc1; 0x65; 0xfa; 0xe4;
                           (* VPSUBD (%_% ymm4) (%_% ymm3) (%_% ymm12) *)
  0xc5; 0xe5; 0xfe; 0xe3;  (* VPADDD (%_% ymm4) (%_% ymm3) (%_% ymm3) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xf5; 0xaa;
                           (* VPBLENDD (%_% ymm14) (%_% ymm13) (%_% ymm13) (Imm8 (word 170)) *)
  0xc5; 0x1d; 0xfe; 0xec;  (* VPADDD (%_% ymm13) (%_% ymm12) (%_% ymm4) *)
  0xc5; 0x65; 0xfa; 0xeb;  (* VPSUBD (%_% ymm13) (%_% ymm3) (%_% ymm3) *)
  0xc4; 0xc2; 0x25; 0x28; 0xcd;
                           (* VPMULDQ (%_% ymm1) (%_% ymm11) (%_% ymm13) *)
  0xc4; 0x41; 0x7e; 0x16; 0xdc;
                           (* VMOVSHDUP (%_% ymm11) (%_% ymm12) *)
  0xc4; 0xc2; 0x1d; 0x28; 0xce;
                           (* VPMULDQ (%_% ymm1) (%_% ymm12) (%_% ymm14) *)
  0xc4; 0xc2; 0x25; 0x28; 0xd3;
                           (* VPMULDQ (%_% ymm2) (%_% ymm11) (%_% ymm11) *)
  0xc4; 0xc2; 0x1d; 0x28; 0xd4;
                           (* VPMULDQ (%_% ymm2) (%_% ymm12) (%_% ymm12) *)
  0xc4; 0xc2; 0x15; 0x28; 0xc5;
                           (* VPMULDQ (%_% ymm0) (%_% ymm13) (%_% ymm13) *)
  0xc4; 0xc2; 0x0d; 0x28; 0xc6;
                           (* VPMULDQ (%_% ymm0) (%_% ymm14) (%_% ymm14) *)
  0xc4; 0x41; 0x7e; 0x16; 0xdb;
                           (* VMOVSHDUP (%_% ymm11) (%_% ymm11) *)
  0xc4; 0x43; 0x25; 0x02; 0xe3; 0xaa;
                           (* VPBLENDD (%_% ymm12) (%_% ymm11) (%_% ymm11) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x2d; 0xfa; 0xdc;
                           (* VPSUBD (%_% ymm11) (%_% ymm10) (%_% ymm12) *)
  0xc4; 0x41; 0x2d; 0xfe; 0xda;
                           (* VPADDD (%_% ymm11) (%_% ymm10) (%_% ymm10) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xf5; 0xaa;
                           (* VPBLENDD (%_% ymm14) (%_% ymm13) (%_% ymm13) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x1d; 0xfe; 0xeb;
                           (* VPADDD (%_% ymm13) (%_% ymm12) (%_% ymm11) *)
  0xc4; 0x41; 0x2d; 0xfa; 0xea;
                           (* VPSUBD (%_% ymm13) (%_% ymm10) (%_% ymm10) *)
  0xc4; 0x41; 0x7e; 0x12; 0xc8;
                           (* VMOVSLDUP (%_% ymm9) (%_% ymm8) *)
  0xc4; 0x63; 0x35; 0x02; 0xcf; 0xaa;
                           (* VPBLENDD (%_% ymm9) (%_% ymm9) (%_% ymm7) (Imm8 (word 170)) *)
  0xc5; 0xc5; 0x73; 0xd7; 0x20;
                           (* VPSRLQ (%_% ymm7) (%_% ymm7) (Imm8 (word 32)) *)
  0xc4; 0x63; 0x3d; 0x02; 0xc7; 0xaa;
                           (* VPBLENDD (%_% ymm8) (%_% ymm8) (%_% ymm7) (Imm8 (word 170)) *)
  0xc5; 0xfe; 0x12; 0xfe;  (* VMOVSLDUP (%_% ymm7) (%_% ymm6) *)
  0xc4; 0xe3; 0x45; 0x02; 0xfd; 0xaa;
                           (* VPBLENDD (%_% ymm7) (%_% ymm7) (%_% ymm5) (Imm8 (word 170)) *)
  0xc5; 0xd5; 0x73; 0xd5; 0x20;
                           (* VPSRLQ (%_% ymm5) (%_% ymm5) (Imm8 (word 32)) *)
  0xc4; 0xe3; 0x4d; 0x02; 0xf5; 0xaa;
                           (* VPBLENDD (%_% ymm6) (%_% ymm6) (%_% ymm5) (Imm8 (word 170)) *)
  0xc5; 0xfe; 0x12; 0xec;  (* VMOVSLDUP (%_% ymm5) (%_% ymm4) *)
  0xc4; 0xe3; 0x55; 0x02; 0xeb; 0xaa;
                           (* VPBLENDD (%_% ymm5) (%_% ymm5) (%_% ymm3) (Imm8 (word 170)) *)
  0xc5; 0xe5; 0x73; 0xd3; 0x20;
                           (* VPSRLQ (%_% ymm3) (%_% ymm3) (Imm8 (word 32)) *)
  0xc4; 0xe3; 0x5d; 0x02; 0xe3; 0xaa;
                           (* VPBLENDD (%_% ymm4) (%_% ymm4) (%_% ymm3) (Imm8 (word 170)) *)
  0xc4; 0xc1; 0x7e; 0x12; 0xdb;
                           (* VMOVSLDUP (%_% ymm3) (%_% ymm11) *)
  0xc4; 0xc3; 0x65; 0x02; 0xda; 0xaa;
                           (* VPBLENDD (%_% ymm3) (%_% ymm3) (%_% ymm10) (Imm8 (word 170)) *)
  0xc4; 0xc1; 0x2d; 0x73; 0xd2; 0x20;
                           (* VPSRLQ (%_% ymm10) (%_% ymm10) (Imm8 (word 32)) *)
  0xc4; 0x43; 0x25; 0x02; 0xda; 0xaa;
                           (* VPBLENDD (%_% ymm11) (%_% ymm11) (%_% ymm10) (Imm8 (word 170)) *)
  0xc5; 0xfd; 0x6f; 0x8e; 0x00; 0x02; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm1) (Memop Word256 (%% (rsi,512))) *)
  0xc5; 0xfd; 0x6f; 0x96; 0xa0; 0x06; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm2) (Memop Word256 (%% (rsi,1696))) *)
  0xc4; 0xc1; 0x75; 0x73; 0xd2; 0x20;
                           (* VPSRLQ (%_% ymm1) (%_% ymm10) (Imm8 (word 32)) *)
  0xc4; 0xc1; 0x7e; 0x16; 0xd7;
                           (* VMOVSHDUP (%_% ymm2) (%_% ymm15) *)
  0xc4; 0xc2; 0x55; 0x28; 0xcd;
                           (* VPMULDQ (%_% ymm1) (%_% ymm5) (%_% ymm13) *)
  0xc4; 0xc1; 0x7e; 0x16; 0xec;
                           (* VMOVSHDUP (%_% ymm5) (%_% ymm12) *)
  0xc4; 0x42; 0x1d; 0x28; 0xd6;
                           (* VPMULDQ (%_% ymm10) (%_% ymm12) (%_% ymm14) *)
  0xc4; 0xe2; 0x55; 0x28; 0xd5;
                           (* VPMULDQ (%_% ymm2) (%_% ymm5) (%_% ymm5) *)
  0xc4; 0x42; 0x1d; 0x28; 0xfc;
                           (* VPMULDQ (%_% ymm15) (%_% ymm12) (%_% ymm12) *)
  0xc4; 0xc2; 0x15; 0x28; 0xc5;
                           (* VPMULDQ (%_% ymm0) (%_% ymm13) (%_% ymm13) *)
  0xc4; 0xc2; 0x0d; 0x28; 0xc6;
                           (* VPMULDQ (%_% ymm0) (%_% ymm14) (%_% ymm14) *)
  0xc5; 0xfe; 0x16; 0xed;  (* VMOVSHDUP (%_% ymm5) (%_% ymm5) *)
  0xc4; 0x63; 0x55; 0x02; 0xe5; 0xaa;
                           (* VPBLENDD (%_% ymm12) (%_% ymm5) (%_% ymm5) (Imm8 (word 170)) *)
  0xc4; 0xc1; 0x35; 0xfa; 0xec;
                           (* VPSUBD (%_% ymm5) (%_% ymm9) (%_% ymm12) *)
  0xc4; 0xc1; 0x35; 0xfe; 0xe9;
                           (* VPADDD (%_% ymm5) (%_% ymm9) (%_% ymm9) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xf5; 0xaa;
                           (* VPBLENDD (%_% ymm14) (%_% ymm13) (%_% ymm13) (Imm8 (word 170)) *)
  0xc5; 0x1d; 0xfe; 0xed;  (* VPADDD (%_% ymm13) (%_% ymm12) (%_% ymm5) *)
  0xc4; 0x41; 0x35; 0xfa; 0xe9;
                           (* VPSUBD (%_% ymm13) (%_% ymm9) (%_% ymm9) *)
  0xc4; 0xc2; 0x5d; 0x28; 0xcd;
                           (* VPMULDQ (%_% ymm1) (%_% ymm4) (%_% ymm13) *)
  0xc4; 0xc1; 0x7e; 0x16; 0xe4;
                           (* VMOVSHDUP (%_% ymm4) (%_% ymm12) *)
  0xc4; 0x42; 0x1d; 0x28; 0xd6;
                           (* VPMULDQ (%_% ymm10) (%_% ymm12) (%_% ymm14) *)
  0xc4; 0xe2; 0x5d; 0x28; 0xd4;
                           (* VPMULDQ (%_% ymm2) (%_% ymm4) (%_% ymm4) *)
  0xc4; 0x42; 0x1d; 0x28; 0xfc;
                           (* VPMULDQ (%_% ymm15) (%_% ymm12) (%_% ymm12) *)
  0xc4; 0xc2; 0x15; 0x28; 0xc5;
                           (* VPMULDQ (%_% ymm0) (%_% ymm13) (%_% ymm13) *)
  0xc4; 0xc2; 0x0d; 0x28; 0xc6;
                           (* VPMULDQ (%_% ymm0) (%_% ymm14) (%_% ymm14) *)
  0xc5; 0xfe; 0x16; 0xe4;  (* VMOVSHDUP (%_% ymm4) (%_% ymm4) *)
  0xc4; 0x63; 0x5d; 0x02; 0xe4; 0xaa;
                           (* VPBLENDD (%_% ymm12) (%_% ymm4) (%_% ymm4) (Imm8 (word 170)) *)
  0xc4; 0xc1; 0x3d; 0xfa; 0xe4;
                           (* VPSUBD (%_% ymm4) (%_% ymm8) (%_% ymm12) *)
  0xc4; 0xc1; 0x3d; 0xfe; 0xe0;
                           (* VPADDD (%_% ymm4) (%_% ymm8) (%_% ymm8) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xf5; 0xaa;
                           (* VPBLENDD (%_% ymm14) (%_% ymm13) (%_% ymm13) (Imm8 (word 170)) *)
  0xc5; 0x1d; 0xfe; 0xec;  (* VPADDD (%_% ymm13) (%_% ymm12) (%_% ymm4) *)
  0xc4; 0x41; 0x3d; 0xfa; 0xe8;
                           (* VPSUBD (%_% ymm13) (%_% ymm8) (%_% ymm8) *)
  0xc4; 0xc2; 0x65; 0x28; 0xcd;
                           (* VPMULDQ (%_% ymm1) (%_% ymm3) (%_% ymm13) *)
  0xc4; 0xc1; 0x7e; 0x16; 0xdc;
                           (* VMOVSHDUP (%_% ymm3) (%_% ymm12) *)
  0xc4; 0x42; 0x1d; 0x28; 0xd6;
                           (* VPMULDQ (%_% ymm10) (%_% ymm12) (%_% ymm14) *)
  0xc4; 0xe2; 0x65; 0x28; 0xd3;
                           (* VPMULDQ (%_% ymm2) (%_% ymm3) (%_% ymm3) *)
  0xc4; 0x42; 0x1d; 0x28; 0xfc;
                           (* VPMULDQ (%_% ymm15) (%_% ymm12) (%_% ymm12) *)
  0xc4; 0xc2; 0x15; 0x28; 0xc5;
                           (* VPMULDQ (%_% ymm0) (%_% ymm13) (%_% ymm13) *)
  0xc4; 0xc2; 0x0d; 0x28; 0xc6;
                           (* VPMULDQ (%_% ymm0) (%_% ymm14) (%_% ymm14) *)
  0xc5; 0xfe; 0x16; 0xdb;  (* VMOVSHDUP (%_% ymm3) (%_% ymm3) *)
  0xc4; 0x63; 0x65; 0x02; 0xe3; 0xaa;
                           (* VPBLENDD (%_% ymm12) (%_% ymm3) (%_% ymm3) (Imm8 (word 170)) *)
  0xc4; 0xc1; 0x45; 0xfa; 0xdc;
                           (* VPSUBD (%_% ymm3) (%_% ymm7) (%_% ymm12) *)
  0xc5; 0xc5; 0xfe; 0xdf;  (* VPADDD (%_% ymm3) (%_% ymm7) (%_% ymm7) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xf5; 0xaa;
                           (* VPBLENDD (%_% ymm14) (%_% ymm13) (%_% ymm13) (Imm8 (word 170)) *)
  0xc5; 0x1d; 0xfe; 0xeb;  (* VPADDD (%_% ymm13) (%_% ymm12) (%_% ymm3) *)
  0xc5; 0x45; 0xfa; 0xef;  (* VPSUBD (%_% ymm13) (%_% ymm7) (%_% ymm7) *)
  0xc4; 0xc2; 0x25; 0x28; 0xcd;
                           (* VPMULDQ (%_% ymm1) (%_% ymm11) (%_% ymm13) *)
  0xc4; 0x41; 0x7e; 0x16; 0xdc;
                           (* VMOVSHDUP (%_% ymm11) (%_% ymm12) *)
  0xc4; 0x42; 0x1d; 0x28; 0xd6;
                           (* VPMULDQ (%_% ymm10) (%_% ymm12) (%_% ymm14) *)
  0xc4; 0xc2; 0x25; 0x28; 0xd3;
                           (* VPMULDQ (%_% ymm2) (%_% ymm11) (%_% ymm11) *)
  0xc4; 0x42; 0x1d; 0x28; 0xfc;
                           (* VPMULDQ (%_% ymm15) (%_% ymm12) (%_% ymm12) *)
  0xc4; 0xc2; 0x15; 0x28; 0xc5;
                           (* VPMULDQ (%_% ymm0) (%_% ymm13) (%_% ymm13) *)
  0xc4; 0xc2; 0x0d; 0x28; 0xc6;
                           (* VPMULDQ (%_% ymm0) (%_% ymm14) (%_% ymm14) *)
  0xc4; 0x41; 0x7e; 0x16; 0xdb;
                           (* VMOVSHDUP (%_% ymm11) (%_% ymm11) *)
  0xc4; 0x43; 0x25; 0x02; 0xe3; 0xaa;
                           (* VPBLENDD (%_% ymm12) (%_% ymm11) (%_% ymm11) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x4d; 0xfa; 0xdc;
                           (* VPSUBD (%_% ymm11) (%_% ymm6) (%_% ymm12) *)
  0xc5; 0x4d; 0xfe; 0xde;  (* VPADDD (%_% ymm11) (%_% ymm6) (%_% ymm6) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xf5; 0xaa;
                           (* VPBLENDD (%_% ymm14) (%_% ymm13) (%_% ymm13) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x1d; 0xfe; 0xeb;
                           (* VPADDD (%_% ymm13) (%_% ymm12) (%_% ymm11) *)
  0xc5; 0x4d; 0xfa; 0xee;  (* VPSUBD (%_% ymm13) (%_% ymm6) (%_% ymm6) *)
  0xc5; 0xfd; 0x6f; 0x8e; 0x80; 0x02; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm1) (Memop Word256 (%% (rsi,640))) *)
  0xc5; 0xfd; 0x6f; 0x96; 0x20; 0x07; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm2) (Memop Word256 (%% (rsi,1824))) *)
  0xc4; 0xc1; 0x75; 0x73; 0xd2; 0x20;
                           (* VPSRLQ (%_% ymm1) (%_% ymm10) (Imm8 (word 32)) *)
  0xc4; 0xc1; 0x7e; 0x16; 0xd7;
                           (* VMOVSHDUP (%_% ymm2) (%_% ymm15) *)
  0xc4; 0xc2; 0x45; 0x28; 0xcd;
                           (* VPMULDQ (%_% ymm1) (%_% ymm7) (%_% ymm13) *)
  0xc4; 0xc1; 0x7e; 0x16; 0xfc;
                           (* VMOVSHDUP (%_% ymm7) (%_% ymm12) *)
  0xc4; 0x42; 0x1d; 0x28; 0xd6;
                           (* VPMULDQ (%_% ymm10) (%_% ymm12) (%_% ymm14) *)
  0xc4; 0xe2; 0x45; 0x28; 0xd7;
                           (* VPMULDQ (%_% ymm2) (%_% ymm7) (%_% ymm7) *)
  0xc4; 0x42; 0x1d; 0x28; 0xfc;
                           (* VPMULDQ (%_% ymm15) (%_% ymm12) (%_% ymm12) *)
  0xc4; 0xc2; 0x15; 0x28; 0xc5;
                           (* VPMULDQ (%_% ymm0) (%_% ymm13) (%_% ymm13) *)
  0xc4; 0xc2; 0x0d; 0x28; 0xc6;
                           (* VPMULDQ (%_% ymm0) (%_% ymm14) (%_% ymm14) *)
  0xc5; 0xfe; 0x16; 0xff;  (* VMOVSHDUP (%_% ymm7) (%_% ymm7) *)
  0xc4; 0x63; 0x45; 0x02; 0xe7; 0xaa;
                           (* VPBLENDD (%_% ymm12) (%_% ymm7) (%_% ymm7) (Imm8 (word 170)) *)
  0xc4; 0xc1; 0x35; 0xfa; 0xfc;
                           (* VPSUBD (%_% ymm7) (%_% ymm9) (%_% ymm12) *)
  0xc4; 0xc1; 0x35; 0xfe; 0xf9;
                           (* VPADDD (%_% ymm7) (%_% ymm9) (%_% ymm9) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xf5; 0xaa;
                           (* VPBLENDD (%_% ymm14) (%_% ymm13) (%_% ymm13) (Imm8 (word 170)) *)
  0xc5; 0x1d; 0xfe; 0xef;  (* VPADDD (%_% ymm13) (%_% ymm12) (%_% ymm7) *)
  0xc4; 0x41; 0x35; 0xfa; 0xe9;
                           (* VPSUBD (%_% ymm13) (%_% ymm9) (%_% ymm9) *)
  0xc4; 0xc2; 0x4d; 0x28; 0xcd;
                           (* VPMULDQ (%_% ymm1) (%_% ymm6) (%_% ymm13) *)
  0xc4; 0xc1; 0x7e; 0x16; 0xf4;
                           (* VMOVSHDUP (%_% ymm6) (%_% ymm12) *)
  0xc4; 0x42; 0x1d; 0x28; 0xd6;
                           (* VPMULDQ (%_% ymm10) (%_% ymm12) (%_% ymm14) *)
  0xc4; 0xe2; 0x4d; 0x28; 0xd6;
                           (* VPMULDQ (%_% ymm2) (%_% ymm6) (%_% ymm6) *)
  0xc4; 0x42; 0x1d; 0x28; 0xfc;
                           (* VPMULDQ (%_% ymm15) (%_% ymm12) (%_% ymm12) *)
  0xc4; 0xc2; 0x15; 0x28; 0xc5;
                           (* VPMULDQ (%_% ymm0) (%_% ymm13) (%_% ymm13) *)
  0xc4; 0xc2; 0x0d; 0x28; 0xc6;
                           (* VPMULDQ (%_% ymm0) (%_% ymm14) (%_% ymm14) *)
  0xc5; 0xfe; 0x16; 0xf6;  (* VMOVSHDUP (%_% ymm6) (%_% ymm6) *)
  0xc4; 0x63; 0x4d; 0x02; 0xe6; 0xaa;
                           (* VPBLENDD (%_% ymm12) (%_% ymm6) (%_% ymm6) (Imm8 (word 170)) *)
  0xc4; 0xc1; 0x3d; 0xfa; 0xf4;
                           (* VPSUBD (%_% ymm6) (%_% ymm8) (%_% ymm12) *)
  0xc4; 0xc1; 0x3d; 0xfe; 0xf0;
                           (* VPADDD (%_% ymm6) (%_% ymm8) (%_% ymm8) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xf5; 0xaa;
                           (* VPBLENDD (%_% ymm14) (%_% ymm13) (%_% ymm13) (Imm8 (word 170)) *)
  0xc5; 0x1d; 0xfe; 0xee;  (* VPADDD (%_% ymm13) (%_% ymm12) (%_% ymm6) *)
  0xc4; 0x41; 0x3d; 0xfa; 0xe8;
                           (* VPSUBD (%_% ymm13) (%_% ymm8) (%_% ymm8) *)
  0xc5; 0xfd; 0x6f; 0x8e; 0x00; 0x03; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm1) (Memop Word256 (%% (rsi,768))) *)
  0xc5; 0xfd; 0x6f; 0x96; 0xa0; 0x07; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm2) (Memop Word256 (%% (rsi,1952))) *)
  0xc4; 0xc1; 0x75; 0x73; 0xd2; 0x20;
                           (* VPSRLQ (%_% ymm1) (%_% ymm10) (Imm8 (word 32)) *)
  0xc4; 0xc1; 0x7e; 0x16; 0xd7;
                           (* VMOVSHDUP (%_% ymm2) (%_% ymm15) *)
  0xc4; 0xc2; 0x65; 0x28; 0xcd;
                           (* VPMULDQ (%_% ymm1) (%_% ymm3) (%_% ymm13) *)
  0xc4; 0xc1; 0x7e; 0x16; 0xdc;
                           (* VMOVSHDUP (%_% ymm3) (%_% ymm12) *)
  0xc4; 0x42; 0x1d; 0x28; 0xd6;
                           (* VPMULDQ (%_% ymm10) (%_% ymm12) (%_% ymm14) *)
  0xc4; 0xe2; 0x65; 0x28; 0xd3;
                           (* VPMULDQ (%_% ymm2) (%_% ymm3) (%_% ymm3) *)
  0xc4; 0x42; 0x1d; 0x28; 0xfc;
                           (* VPMULDQ (%_% ymm15) (%_% ymm12) (%_% ymm12) *)
  0xc4; 0xc2; 0x15; 0x28; 0xc5;
                           (* VPMULDQ (%_% ymm0) (%_% ymm13) (%_% ymm13) *)
  0xc4; 0xc2; 0x0d; 0x28; 0xc6;
                           (* VPMULDQ (%_% ymm0) (%_% ymm14) (%_% ymm14) *)
  0xc5; 0xfe; 0x16; 0xdb;  (* VMOVSHDUP (%_% ymm3) (%_% ymm3) *)
  0xc4; 0x63; 0x65; 0x02; 0xe3; 0xaa;
                           (* VPBLENDD (%_% ymm12) (%_% ymm3) (%_% ymm3) (Imm8 (word 170)) *)
  0xc4; 0xc1; 0x55; 0xfa; 0xdc;
                           (* VPSUBD (%_% ymm3) (%_% ymm5) (%_% ymm12) *)
  0xc5; 0xd5; 0xfe; 0xdd;  (* VPADDD (%_% ymm3) (%_% ymm5) (%_% ymm5) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xf5; 0xaa;
                           (* VPBLENDD (%_% ymm14) (%_% ymm13) (%_% ymm13) (Imm8 (word 170)) *)
  0xc5; 0x1d; 0xfe; 0xeb;  (* VPADDD (%_% ymm13) (%_% ymm12) (%_% ymm3) *)
  0xc5; 0x55; 0xfa; 0xed;  (* VPSUBD (%_% ymm13) (%_% ymm5) (%_% ymm5) *)
  0xc4; 0xc2; 0x25; 0x28; 0xcd;
                           (* VPMULDQ (%_% ymm1) (%_% ymm11) (%_% ymm13) *)
  0xc4; 0x41; 0x7e; 0x16; 0xdc;
                           (* VMOVSHDUP (%_% ymm11) (%_% ymm12) *)
  0xc4; 0x42; 0x1d; 0x28; 0xd6;
                           (* VPMULDQ (%_% ymm10) (%_% ymm12) (%_% ymm14) *)
  0xc4; 0xc2; 0x25; 0x28; 0xd3;
                           (* VPMULDQ (%_% ymm2) (%_% ymm11) (%_% ymm11) *)
  0xc4; 0x42; 0x1d; 0x28; 0xfc;
                           (* VPMULDQ (%_% ymm15) (%_% ymm12) (%_% ymm12) *)
  0xc4; 0xc2; 0x15; 0x28; 0xc5;
                           (* VPMULDQ (%_% ymm0) (%_% ymm13) (%_% ymm13) *)
  0xc4; 0xc2; 0x0d; 0x28; 0xc6;
                           (* VPMULDQ (%_% ymm0) (%_% ymm14) (%_% ymm14) *)
  0xc4; 0x41; 0x7e; 0x16; 0xdb;
                           (* VMOVSHDUP (%_% ymm11) (%_% ymm11) *)
  0xc4; 0x43; 0x25; 0x02; 0xe3; 0xaa;
                           (* VPBLENDD (%_% ymm12) (%_% ymm11) (%_% ymm11) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x5d; 0xfa; 0xdc;
                           (* VPSUBD (%_% ymm11) (%_% ymm4) (%_% ymm12) *)
  0xc5; 0x5d; 0xfe; 0xdc;  (* VPADDD (%_% ymm11) (%_% ymm4) (%_% ymm4) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xf5; 0xaa;
                           (* VPBLENDD (%_% ymm14) (%_% ymm13) (%_% ymm13) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x1d; 0xfe; 0xeb;
                           (* VPADDD (%_% ymm13) (%_% ymm12) (%_% ymm11) *)
  0xc5; 0x5d; 0xfa; 0xec;  (* VPSUBD (%_% ymm13) (%_% ymm4) (%_% ymm4) *)
  0xc5; 0xfd; 0x6f; 0x8e; 0x80; 0x03; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm1) (Memop Word256 (%% (rsi,896))) *)
  0xc5; 0xfd; 0x6f; 0x96; 0x20; 0x08; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm2) (Memop Word256 (%% (rsi,2080))) *)
  0xc4; 0xc1; 0x75; 0x73; 0xd2; 0x20;
                           (* VPSRLQ (%_% ymm1) (%_% ymm10) (Imm8 (word 32)) *)
  0xc4; 0xc1; 0x7e; 0x16; 0xd7;
                           (* VMOVSHDUP (%_% ymm2) (%_% ymm15) *)
  0xc4; 0xc2; 0x3d; 0x28; 0xcd;
                           (* VPMULDQ (%_% ymm1) (%_% ymm8) (%_% ymm13) *)
  0xc4; 0x41; 0x7e; 0x16; 0xc4;
                           (* VMOVSHDUP (%_% ymm8) (%_% ymm12) *)
  0xc4; 0x42; 0x1d; 0x28; 0xd6;
                           (* VPMULDQ (%_% ymm10) (%_% ymm12) (%_% ymm14) *)
  0xc4; 0xc2; 0x3d; 0x28; 0xd0;
                           (* VPMULDQ (%_% ymm2) (%_% ymm8) (%_% ymm8) *)
  0xc4; 0x42; 0x1d; 0x28; 0xfc;
                           (* VPMULDQ (%_% ymm15) (%_% ymm12) (%_% ymm12) *)
  0xc4; 0xc2; 0x15; 0x28; 0xc5;
                           (* VPMULDQ (%_% ymm0) (%_% ymm13) (%_% ymm13) *)
  0xc4; 0xc2; 0x0d; 0x28; 0xc6;
                           (* VPMULDQ (%_% ymm0) (%_% ymm14) (%_% ymm14) *)
  0xc4; 0x41; 0x7e; 0x16; 0xc0;
                           (* VMOVSHDUP (%_% ymm8) (%_% ymm8) *)
  0xc4; 0x43; 0x3d; 0x02; 0xe0; 0xaa;
                           (* VPBLENDD (%_% ymm12) (%_% ymm8) (%_% ymm8) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x35; 0xfa; 0xc4;
                           (* VPSUBD (%_% ymm8) (%_% ymm9) (%_% ymm12) *)
  0xc4; 0x41; 0x35; 0xfe; 0xc1;
                           (* VPADDD (%_% ymm8) (%_% ymm9) (%_% ymm9) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xf5; 0xaa;
                           (* VPBLENDD (%_% ymm14) (%_% ymm13) (%_% ymm13) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x1d; 0xfe; 0xe8;
                           (* VPADDD (%_% ymm13) (%_% ymm12) (%_% ymm8) *)
  0xc4; 0x41; 0x35; 0xfa; 0xe9;
                           (* VPSUBD (%_% ymm13) (%_% ymm9) (%_% ymm9) *)
  0xc5; 0xfd; 0x6f; 0x8e; 0x00; 0x04; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm1) (Memop Word256 (%% (rsi,1024))) *)
  0xc5; 0xfd; 0x6f; 0x96; 0xa0; 0x08; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm2) (Memop Word256 (%% (rsi,2208))) *)
  0xc4; 0xc1; 0x75; 0x73; 0xd2; 0x20;
                           (* VPSRLQ (%_% ymm1) (%_% ymm10) (Imm8 (word 32)) *)
  0xc4; 0xc1; 0x7e; 0x16; 0xd7;
                           (* VMOVSHDUP (%_% ymm2) (%_% ymm15) *)
  0xc4; 0xc2; 0x4d; 0x28; 0xcd;
                           (* VPMULDQ (%_% ymm1) (%_% ymm6) (%_% ymm13) *)
  0xc4; 0xc1; 0x7e; 0x16; 0xf4;
                           (* VMOVSHDUP (%_% ymm6) (%_% ymm12) *)
  0xc4; 0x42; 0x1d; 0x28; 0xd6;
                           (* VPMULDQ (%_% ymm10) (%_% ymm12) (%_% ymm14) *)
  0xc4; 0xe2; 0x4d; 0x28; 0xd6;
                           (* VPMULDQ (%_% ymm2) (%_% ymm6) (%_% ymm6) *)
  0xc4; 0x42; 0x1d; 0x28; 0xfc;
                           (* VPMULDQ (%_% ymm15) (%_% ymm12) (%_% ymm12) *)
  0xc4; 0xc2; 0x15; 0x28; 0xc5;
                           (* VPMULDQ (%_% ymm0) (%_% ymm13) (%_% ymm13) *)
  0xc4; 0xc2; 0x0d; 0x28; 0xc6;
                           (* VPMULDQ (%_% ymm0) (%_% ymm14) (%_% ymm14) *)
  0xc5; 0xfe; 0x16; 0xf6;  (* VMOVSHDUP (%_% ymm6) (%_% ymm6) *)
  0xc4; 0x63; 0x4d; 0x02; 0xe6; 0xaa;
                           (* VPBLENDD (%_% ymm12) (%_% ymm6) (%_% ymm6) (Imm8 (word 170)) *)
  0xc4; 0xc1; 0x45; 0xfa; 0xf4;
                           (* VPSUBD (%_% ymm6) (%_% ymm7) (%_% ymm12) *)
  0xc5; 0xc5; 0xfe; 0xf7;  (* VPADDD (%_% ymm6) (%_% ymm7) (%_% ymm7) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xf5; 0xaa;
                           (* VPBLENDD (%_% ymm14) (%_% ymm13) (%_% ymm13) (Imm8 (word 170)) *)
  0xc5; 0x1d; 0xfe; 0xee;  (* VPADDD (%_% ymm13) (%_% ymm12) (%_% ymm6) *)
  0xc5; 0x45; 0xfa; 0xef;  (* VPSUBD (%_% ymm13) (%_% ymm7) (%_% ymm7) *)
  0xc5; 0xfd; 0x6f; 0x8e; 0x80; 0x04; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm1) (Memop Word256 (%% (rsi,1152))) *)
  0xc5; 0xfd; 0x6f; 0x96; 0x20; 0x09; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm2) (Memop Word256 (%% (rsi,2336))) *)
  0xc4; 0xc1; 0x75; 0x73; 0xd2; 0x20;
                           (* VPSRLQ (%_% ymm1) (%_% ymm10) (Imm8 (word 32)) *)
  0xc4; 0xc1; 0x7e; 0x16; 0xd7;
                           (* VMOVSHDUP (%_% ymm2) (%_% ymm15) *)
  0xc4; 0xc2; 0x5d; 0x28; 0xcd;
                           (* VPMULDQ (%_% ymm1) (%_% ymm4) (%_% ymm13) *)
  0xc4; 0xc1; 0x7e; 0x16; 0xe4;
                           (* VMOVSHDUP (%_% ymm4) (%_% ymm12) *)
  0xc4; 0x42; 0x1d; 0x28; 0xd6;
                           (* VPMULDQ (%_% ymm10) (%_% ymm12) (%_% ymm14) *)
  0xc4; 0xe2; 0x5d; 0x28; 0xd4;
                           (* VPMULDQ (%_% ymm2) (%_% ymm4) (%_% ymm4) *)
  0xc4; 0x42; 0x1d; 0x28; 0xfc;
                           (* VPMULDQ (%_% ymm15) (%_% ymm12) (%_% ymm12) *)
  0xc4; 0xc2; 0x15; 0x28; 0xc5;
                           (* VPMULDQ (%_% ymm0) (%_% ymm13) (%_% ymm13) *)
  0xc4; 0xc2; 0x0d; 0x28; 0xc6;
                           (* VPMULDQ (%_% ymm0) (%_% ymm14) (%_% ymm14) *)
  0xc5; 0xfe; 0x16; 0xe4;  (* VMOVSHDUP (%_% ymm4) (%_% ymm4) *)
  0xc4; 0x63; 0x5d; 0x02; 0xe4; 0xaa;
                           (* VPBLENDD (%_% ymm12) (%_% ymm4) (%_% ymm4) (Imm8 (word 170)) *)
  0xc4; 0xc1; 0x55; 0xfa; 0xe4;
                           (* VPSUBD (%_% ymm4) (%_% ymm5) (%_% ymm12) *)
  0xc5; 0xd5; 0xfe; 0xe5;  (* VPADDD (%_% ymm4) (%_% ymm5) (%_% ymm5) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xf5; 0xaa;
                           (* VPBLENDD (%_% ymm14) (%_% ymm13) (%_% ymm13) (Imm8 (word 170)) *)
  0xc5; 0x1d; 0xfe; 0xec;  (* VPADDD (%_% ymm13) (%_% ymm12) (%_% ymm4) *)
  0xc5; 0x55; 0xfa; 0xed;  (* VPSUBD (%_% ymm13) (%_% ymm5) (%_% ymm5) *)
  0xc5; 0xfd; 0x6f; 0x8e; 0x00; 0x05; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm1) (Memop Word256 (%% (rsi,1280))) *)
  0xc5; 0xfd; 0x6f; 0x96; 0xa0; 0x09; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm2) (Memop Word256 (%% (rsi,2464))) *)
  0xc4; 0xc1; 0x75; 0x73; 0xd2; 0x20;
                           (* VPSRLQ (%_% ymm1) (%_% ymm10) (Imm8 (word 32)) *)
  0xc4; 0xc1; 0x7e; 0x16; 0xd7;
                           (* VMOVSHDUP (%_% ymm2) (%_% ymm15) *)
  0xc4; 0xc2; 0x25; 0x28; 0xcd;
                           (* VPMULDQ (%_% ymm1) (%_% ymm11) (%_% ymm13) *)
  0xc4; 0x41; 0x7e; 0x16; 0xdc;
                           (* VMOVSHDUP (%_% ymm11) (%_% ymm12) *)
  0xc4; 0x42; 0x1d; 0x28; 0xd6;
                           (* VPMULDQ (%_% ymm10) (%_% ymm12) (%_% ymm14) *)
  0xc4; 0xc2; 0x25; 0x28; 0xd3;
                           (* VPMULDQ (%_% ymm2) (%_% ymm11) (%_% ymm11) *)
  0xc4; 0x42; 0x1d; 0x28; 0xfc;
                           (* VPMULDQ (%_% ymm15) (%_% ymm12) (%_% ymm12) *)
  0xc4; 0xc2; 0x15; 0x28; 0xc5;
                           (* VPMULDQ (%_% ymm0) (%_% ymm13) (%_% ymm13) *)
  0xc4; 0xc2; 0x0d; 0x28; 0xc6;
                           (* VPMULDQ (%_% ymm0) (%_% ymm14) (%_% ymm14) *)
  0xc4; 0x41; 0x7e; 0x16; 0xdb;
                           (* VMOVSHDUP (%_% ymm11) (%_% ymm11) *)
  0xc4; 0x43; 0x25; 0x02; 0xe3; 0xaa;
                           (* VPBLENDD (%_% ymm12) (%_% ymm11) (%_% ymm11) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x65; 0xfa; 0xdc;
                           (* VPSUBD (%_% ymm11) (%_% ymm3) (%_% ymm12) *)
  0xc5; 0x65; 0xfe; 0xdb;  (* VPADDD (%_% ymm11) (%_% ymm3) (%_% ymm3) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xf5; 0xaa;
                           (* VPBLENDD (%_% ymm14) (%_% ymm13) (%_% ymm13) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x1d; 0xfe; 0xeb;
                           (* VPADDD (%_% ymm13) (%_% ymm12) (%_% ymm11) *)
  0xc5; 0x65; 0xfa; 0xeb;  (* VPSUBD (%_% ymm13) (%_% ymm3) (%_% ymm3) *)
  0xc5; 0x7d; 0x7f; 0x8f; 0x00; 0x03; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,768))) (%_% ymm9) *)
  0xc5; 0x7d; 0x7f; 0x87; 0x20; 0x03; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,800))) (%_% ymm8) *)
  0xc5; 0xfd; 0x7f; 0xbf; 0x40; 0x03; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,832))) (%_% ymm7) *)
  0xc5; 0xfd; 0x7f; 0xb7; 0x60; 0x03; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,864))) (%_% ymm6) *)
  0xc5; 0xfd; 0x7f; 0xaf; 0x80; 0x03; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,896))) (%_% ymm5) *)
  0xc5; 0xfd; 0x7f; 0xa7; 0xa0; 0x03; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,928))) (%_% ymm4) *)
  0xc5; 0xfd; 0x7f; 0x9f; 0xc0; 0x03; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,960))) (%_% ymm3) *)
  0xc5; 0x7d; 0x7f; 0x9f; 0xe0; 0x03; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,992))) (%_% ymm11) *)
  0xc3                     (* RET *)
];;

let mldsa_ntt_tmc = define_trimmed "mldsa_ntt_tmc" mldsa_ntt_mc;;
let MLDSA_NTT_TMC_EXEC = X86_MK_CORE_EXEC_RULE mldsa_ntt_tmc;;

(*** getting PC length/size:
let len_thm = REWRITE_CONV[mldsa_ntt_tmc] `LENGTH mldsa_ntt_tmc` in
let len_computed = LENGTH_CONV (rhs (concl len_thm)) in
let final_value = rhs (concl len_computed) in
dest_small_numeral final_value;;

val it : int = 12401
pc + 0x3070 ***)

(* ------------------------------------------------------------------------- *)
(* Data tables that are assumed in the precondition.                         *)
(* ------------------------------------------------------------------------- *)

let mldsa_zetas_optimized_twiddles = define
 `mldsa_zetas_optimized_twiddles:int list =
   [-- &3975713; &25847; -- &2608894; -- &518909; &237124; -- &777960; -- &876248; &466468; &1826347; &1826347; &1826347;
    &1826347; &2353451; &2353451; &2353451; &2353451; -- &359251; -- &359251; -- &359251; -- &359251; -- &2091905;
    -- &2091905; -- &2091905; -- &2091905; &3119733; &3119733; &3119733; &3119733; -- &2884855; -- &2884855; -- &2884855;
    -- &2884855; &3111497; &3111497; &3111497; &3111497; &2680103; &2680103; &2680103; &2680103; &2725464;
    &2725464; &1024112; &1024112; -- &1079900; -- &1079900; &3585928; &3585928; -- &549488; -- &549488; -- &1119584;
    -- &1119584; &2619752; &2619752; -- &2108549; -- &2108549; -- &2118186; -- &2118186; -- &3859737; -- &3859737;
    -- &1399561; -- &1399561; -- &3277672; -- &3277672; &1757237; &1757237; -- &19422; -- &19422; &4010497; &4010497;
    &280005; &280005; &2706023; &95776; &3077325; &3530437; -- &1661693; -- &3592148; -- &2537516; &3915439;
    -- &3861115; -- &3043716; &3574422; -- &2867647; &3539968; -- &300467; &2348700; -- &539299; -- &1699267; -- &1643818;
    &3505694; -- &3821735; &3507263; -- &2140649; -- &1600420; &3699596; &811944; &531354; &954230; &3881043;
    &3900724; -- &2556880; &2071892; -- &2797779; -- &3930395; -- &3677745; -- &1452451; &2176455; -- &1257611; -- &4083598;
    -- &3190144; -- &3632928; &3412210; &2147896; -- &2967645; -- &411027; -- &671102; -- &22981; -- &1308169; -- &381987;
    &1852771; -- &1430430; -- &3343383; &508951; &44288; &904516; -- &3724342; &1653064; &2389356; &759969; &189548; &3159746;
    -- &2409325; &1315589; &1341330; &1285669; -- &1584928; -- &812732; -- &1439742; -- &3019102; -- &3881060;
    -- &3628969; &3839961; &2091667; &3407706; &2316500; &3817976; -- &3342478; &2244091; -- &2446433; -- &3562462; &266997;
    &2434439; -- &1235728; &3513181; -- &3520352; -- &3759364; -- &1197226; -- &3193378; &900702; &1859098; &909542;
    &819034; &495491; -- &1613174; -- &43260; -- &522500; -- &655327; -- &3122442; &2031748; &3207046; -- &3556995; -- &525098;
    -- &768622; -- &3595838; &342297; &286988; -- &2437823; &4108315; &3437287; -- &3342277; &1735879; &203044;
    &2842341; &2691481; -- &2590150; &1265009; &4055324; &1247620; &2486353; &1595974; -- &3767016; &1250494; &2635921;
    -- &3548272; -- &2994039; &1869119; &1903435; -- &1050970; -- &1333058; &1237275; -- &3318210; -- &1430225; -- &451100;
    &1312455; &3306115; -- &1962642; -- &1279661; &1917081; -- &2546312; -- &1374803; &1500165; &777191; &2235880; &3406031;
    -- &542412; -- &2831860; -- &1671176; -- &1846953; -- &2584293; -- &3724270; &594136; -- &3776993; -- &2013608; &2432395;
    &2454455; -- &164721; &1957272; &3369112; &185531; -- &1207385; -- &3183426; &162844; &1616392; &3014001; &810149;
    &1652634; -- &3694233; -- &1799107; -- &3038916; &3523897; &3866901; &269760; &2213111; -- &975884; &1717735;
    &472078; -- &426683; &1723600; -- &1803090; &1910376; -- &1667432; -- &1104333; -- &260646; -- &3833893; -- &2939036;
    -- &2235985; -- &420899; -- &2286327; &183443; -- &976891; &1612842; -- &3545687; -- &554416; &3919660; -- &48306;
    -- &1362209; &3937738; &1400424; -- &846154; &1976782]`;;


(* ------------------------------------------------------------------------- *)
(* Correctness proof.                                                        *)
(* ------------------------------------------------------------------------- *)

g(`!a zetas x pc.
      aligned 32 a /\
      aligned 32 zetas /\
      nonoverlapping (word pc,0x3070) (a, 1024) /\
      nonoverlapping (word pc,0x3070) (zetas, 1344) /\
      nonoverlapping (a, 1024) (zetas, 1344)
      ==> ensures x86
           (\s. bytes_loaded s (word pc) (BUTLAST mldsa_ntt_tmc) /\
                read RIP s = word pc /\
                C_ARGUMENTS [a; zetas] s /\
                wordlist_from_memory(zetas,336) s = MAP iword mldsa_zetas_optimized_twiddles /\
                !i. i < 256
                    ==> read(memory :> bytes32(word_add a (word(4 * i)))) s =
                        x i)
           (\s. read RIP s = word(pc + 0x3070) /\
                ((!i. i < 256 ==> abs(ival(x i)) <= &8380416)
                 ==> !i. i < 256
                         ==> let zi =
                        read(memory :> bytes32(word_add a (word(4 * i)))) s in
                        (ival zi == mldsa_forward_ntt (ival o x) i) (mod &8380417) /\
                        abs(ival zi) <= &6283008))
           (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
            MAYCHANGE [ZMM0; ZMM1; ZMM4; ZMM5; ZMM6; ZMM7; ZMM8; ZMM9; ZMM10; ZMM11; ZMM12; ZMM13; ZMM14; ZMM15] ,,
            MAYCHANGE [RAX] ,, MAYCHANGE SOME_FLAGS ,,
            MAYCHANGE [memory :> bytes(a,1024)])`);;


   (* Step 1: First apply the working tactic *)
e(MAP_EVERY X_GEN_TAC
   [`a:int64`; `zetas:int64`; `x:num->int32`; `pc:num`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              NONOVERLAPPING_CLAUSES; ALL] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC));;

(* now getting stuck on Stepping to state s4, first load of Zetas? *)

e(ASM_CASES_TAC
   `zetas_data:int32 list = MAP iword mldsa_zetas_optimized_twiddles` THEN
  ASM_REWRITE_TAC[CONJ_ASSOC] THEN REWRITE_TAC[GSYM CONJ_ASSOC] THENL
   [FIRST_X_ASSUM SUBST1_TAC;
    X86_QUICKSIM_TAC MLDSA_NTT_TMC_EXEC
     [`read RDI s = a`; `read RSI s = zetas`]
     (1--50)]);;
