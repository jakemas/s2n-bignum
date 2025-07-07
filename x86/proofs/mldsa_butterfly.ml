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
let mldsa_butterfly_instance_mc = define_assert_from_elf
 "mldsa_butterfly_instance_mc" "s2n-bignum/x86/mldsa/mldsa_butterfly.o"
[
  (* Machine code will be inserted here using print_literal_from_elf *)
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
  X86_STEPS_TAC mldsa_butterfly_instance_mc [1] THEN
  (* ... continue with simulation steps ... *)
  
  (* Verify the final state *)
  ENSURES_FINAL_STATE_TAC THEN
  ASM_REWRITE_TAC[] THEN
  
  (* Prove that the final state matches the specification *)
  (* ... proof steps ... *)
);;
