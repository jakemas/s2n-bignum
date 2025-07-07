(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* ML-DSA butterfly operation proof.                                         *)
(* ========================================================================= *)

needs "x86/proofs/base.ml";;
needs "x86/proofs/mldsa_constants.ml";;
needs "x86/proofs/mldsa_specs.ml";;
needs "x86/proofs/mldsa_zetas.ml";;

(* Import the machine code from the ELF file *)

(**** print_literal_from_elf "x86/mldsa/mldsa_butterfly.o";;
 ****)

let mldsa_butterfly_instance_mc = define_assert_from_elf
 "mldsa_butterfly_instance_mc" "s2n-bignum/x86/mldsa/mldsa_butterfly.o"
[
  0xc4; 0x42; 0x75; 0x28; 0xe8;
                           (* VPMULDQ (%_% ymm13) (%_% ymm1) (%_% ymm8) *)
  0xc4; 0x41; 0x7e; 0x16; 0xe0;
                           (* VMOVSHDUP (%_% ymm12) (%_% ymm8) *)
  0xc4; 0x42; 0x75; 0x28; 0xf4;
                           (* VPMULDQ (%_% ymm14) (%_% ymm1) (%_% ymm12) *)
  0xc4; 0x42; 0x6d; 0x28; 0xc0;
                           (* VPMULDQ (%_% ymm8) (%_% ymm2) (%_% ymm8) *)
  0xc4; 0x42; 0x6d; 0x28; 0xe4;
                           (* VPMULDQ (%_% ymm12) (%_% ymm2) (%_% ymm12) *)
  0xc4; 0x42; 0x7d; 0x28; 0xed;
                           (* VPMULDQ (%_% ymm13) (%_% ymm0) (%_% ymm13) *)
  0xc4; 0x42; 0x7d; 0x28; 0xf6;
                           (* VPMULDQ (%_% ymm14) (%_% ymm0) (%_% ymm14) *)
  0xc4; 0x41; 0x7e; 0x16; 0xc0;
                           (* VMOVSHDUP (%_% ymm8) (%_% ymm8) *)
  0xc4; 0x43; 0x3d; 0x02; 0xc4; 0xaa;
                           (* VPBLENDD (%_% ymm8) (%_% ymm8) (%_% ymm12) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x5d; 0xfa; 0xe0;
                           (* VPSUBD (%_% ymm12) (%_% ymm4) (%_% ymm8) *)
  0xc4; 0xc1; 0x5d; 0xfe; 0xe0;
                           (* VPADDD (%_% ymm4) (%_% ymm4) (%_% ymm8) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xee; 0xaa;
                           (* VPBLENDD (%_% ymm13) (%_% ymm13) (%_% ymm14) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x1d; 0xfe; 0xc5;
                           (* VPADDD (%_% ymm8) (%_% ymm12) (%_% ymm13) *)
  0xc4; 0xc1; 0x5d; 0xfa; 0xe5;
                           (* VPSUBD (%_% ymm4) (%_% ymm4) (%_% ymm13) *)
  0xc3                     (* RET *)
];;

(* Define the correctness theorem for the butterfly instance *)
let MLDSA_BUTTERFLY_INSTANCE_CORRECT = prove
 (`!l h zl zh q qinv pc.
      (* Preconditions *)
      abs(l) <= &8191 /\
      abs(h) <= &8191 /\
      abs(zl) <= mldsa_q_half /\
      abs(zh) <= mldsa_q_half /\
      q = mldsa_q /\
      qinv = mldsa_qinv
      ==> ensures x86
           (\s. aligned_bytes_loaded s (word pc) mldsa_butterfly_instance_mc /\
                read PC s = word pc /\
                read YMM4 s = l /\
                read YMM8 s = h /\
                read YMM1 s = zl /\
                read YMM2 s = zh /\
                read YMM0 s = qinv)
           (\s. let (l', h') = butterfly_spec l h zl zh q qinv in
                read PC s = word(pc + 0x40) /\
                read YMM4 s = l' /\
                read YMM8 s = h' /\
                abs(read YMM4 s) <= &2*q /\
                abs(read YMM8 s) <= &2*q)
           (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
            MAYCHANGE [YMM12; YMM13; YMM14])`,

  (* Proof steps *)
  MAP_EVERY X_GEN_TAC [`l:int128`; `h:int128`; `zl:int128`; `zh:int128`; `q:int`; `qinv:int`; `pc:num`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  
  (* Initialize the state *)
  ENSURES_INIT_TAC "s0" THEN
  
  (* Simulate the execution of each instruction *)
  X86_STEPS_TAC mldsa_butterfly_instance_mc [1] THEN SIMD_SIMPLIFY_TAC[] THEN
  X86_STEPS_TAC mldsa_butterfly_instance_mc [2] THEN SIMD_SIMPLIFY_TAC[] THEN
  X86_STEPS_TAC mldsa_butterfly_instance_mc [3] THEN SIMD_SIMPLIFY_TAC[] THEN
  X86_STEPS_TAC mldsa_butterfly_instance_mc [4] THEN SIMD_SIMPLIFY_TAC[] THEN
  X86_STEPS_TAC mldsa_butterfly_instance_mc [5] THEN SIMD_SIMPLIFY_TAC[] THEN
  X86_STEPS_TAC mldsa_butterfly_instance_mc [6] THEN SIMD_SIMPLIFY_TAC[] THEN
  X86_STEPS_TAC mldsa_butterfly_instance_mc [7] THEN SIMD_SIMPLIFY_TAC[] THEN
  X86_STEPS_TAC mldsa_butterfly_instance_mc [8] THEN SIMD_SIMPLIFY_TAC[] THEN
  X86_STEPS_TAC mldsa_butterfly_instance_mc [9] THEN SIMD_SIMPLIFY_TAC[] THEN
  X86_STEPS_TAC mldsa_butterfly_instance_mc [10] THEN SIMD_SIMPLIFY_TAC[] THEN
  X86_STEPS_TAC mldsa_butterfly_instance_mc [11] THEN SIMD_SIMPLIFY_TAC[] THEN
  X86_STEPS_TAC mldsa_butterfly_instance_mc [12] THEN SIMD_SIMPLIFY_TAC[] THEN
  X86_STEPS_TAC mldsa_butterfly_instance_mc [13] THEN SIMD_SIMPLIFY_TAC[] THEN
  X86_STEPS_TAC mldsa_butterfly_instance_mc [14] THEN SIMD_SIMPLIFY_TAC[] THEN
  X86_STEPS_TAC mldsa_butterfly_instance_mc [15] THEN SIMD_SIMPLIFY_TAC[] THEN
  X86_STEPS_TAC mldsa_butterfly_instance_mc [16] THEN
  
  (* Verify the final state *)
  ENSURES_FINAL_STATE_TAC THEN
  ASM_REWRITE_TAC[] THEN
  
  (* Prove that the final state matches the specification *)
  REWRITE_TAC[butterfly_spec; LET_DEF; LET_END_DEF] THEN
  REWRITE_TAC[montgomery_multiply] THEN
  SIMP_TAC[GSYM INT_ADD_ASSOC; INT_ADD_LID; INT_ADD_RID] THEN
  SIMP_TAC[INT_MUL_ASSOC; INT_MUL_LID; INT_MUL_RID] THEN
  CONV_TAC INT_REDUCE_CONV THEN
  REWRITE_TAC[] THEN
  CONJ_TAC THENL [
    (* Prove bound for l' *)
    MATCH_MP_TAC INT_BOUNDS_ADD THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC INT_BOUNDS_MUL THEN
    ASM_REWRITE_TAC[] THEN
    CONV_TAC INT_REDUCE_CONV;

    (* Prove bound for h' *)
    MATCH_MP_TAC INT_BOUNDS_SUB THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC INT_BOUNDS_MUL THEN
    ASM_REWRITE_TAC[] THEN
    CONV_TAC INT_REDUCE_CONV
  ]
);;
