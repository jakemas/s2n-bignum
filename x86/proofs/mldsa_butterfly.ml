(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* ML-DSA butterfly operation proof.                                         *)
(* ========================================================================= *)

needs "x86/proofs/base.ml";;

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


(* Define the execution rule *)
let MLDSA_BUTTERFLY_EXEC = X86_MK_EXEC_RULE mldsa_butterfly_instance_mc;;

(* Definitions below can be moved to x86/proofs/mldsa_specs.ml when complete *)

(* Define the modulus q for MLDSA *)
let mldsa_q = define `mldsa_q = 3329`;;

(* Define Montgomery reduction *)
let montgomery_reduce = define
 `montgomery_reduce x = (x DIV (2 EXP 32)) mod mldsa_q`;;

(* Define Montgomery multiplication *)
let montgomery_multiply = define
 `montgomery_multiply a b = montgomery_reduce (a * b)`;;

(* Define the butterfly operation specification *)
let mldsa_butterfly_spec = define
 `mldsa_butterfly_spec l h zeta =
    let t = montgomery_multiply h zeta in
    let l' = (l + t) mod mldsa_q in
    let h' = (l - t) mod mldsa_q in
    (l', h')`;;

(* Main correctness theorem *)
let MLDSA_BUTTERFLY_CORRECT = prove(
  `forall pc l h zeta qinv.
  ensures x86
    (* Precondition *)
    (\s. bytes_loaded s (word pc) mldsa_butterfly_instance_mc /\
         read RIP s = word pc /\
         read YMM0 s = qinv /\
         read YMM1 s = zeta /\
         read YMM4 s = l /\
         read YMM8 s = h)
    (* Postcondition *)
    (\s. read RIP s = word (pc + LENGTH mldsa_butterfly_instance_mc) /\
         let t = (h * zeta) mod mldsa_q in
         read YMM8 s = (l + t) mod mldsa_q /\
         read YMM4 s = (l - t) mod mldsa_q)
    (* Registers that may change *)
    (MAYCHANGE [RIP; YMM8; YMM12; YMM13; YMM14] ,, MAYCHANGE SOME_FLAGS)`,
  
  (* Start the proof *)
  REWRITE_TAC [SOME_FLAGS] THEN
  REPEAT STRIP_TAC THEN
  
  (* Use ENSURES_SEQUENCE_TAC to split the program into chunks *)
  ENSURES_SEQUENCE_TAC
    `pc + 9`  (* Split point after instruction 9 *)
    `\s. read YMM8 s = (h * zeta) mod mldsa_q` THEN
  
  CONJ_TAC THENL [
    (* First chunk: Compute t = h * zeta mod q *)
    ENSURES_INIT_TAC "s0" THEN
    X86_STEPS_TAC MLDSA_BUTTERFLY_EXEC (1--9) THEN
    ENSURES_FINAL_STATE_TAC THEN
    ASM_REWRITE_TAC[] THEN
    (* Prove: Montgomery multiplication computes t correctly *)
    CONV_TAC WORD_RULE;

    (* Second chunk: Compute l' and h' *)
    ENSURES_SEQUENCE_TAC
      `pc + 16`  (* Split point after instruction 16 *)
      `\s. read YMM12 s = (l - (h * zeta) mod mldsa_q) /\
           read YMM8 s = (l + (h * zeta) mod mldsa_q)` THEN
    
    CONJ_TAC THENL [
      (* Compute l' and h' *)
      ENSURES_INIT_TAC "s0" THEN
      X86_STEPS_TAC MLDSA_BUTTERFLY_EXEC (1--7) THEN
      ENSURES_FINAL_STATE_TAC THEN
      ASM_REWRITE_TAC[] THEN
      CONV_TAC WORD_RULE;
      
      (* Final verification *)
      ENSURES_INIT_TAC "s0" THEN
      X86_STEPS_TAC MLDSA_BUTTERFLY_EXEC (1--1) THEN
      ENSURES_FINAL_STATE_TAC THEN
      ASM_REWRITE_TAC[] THEN
      CONV_TAC WORD_RULE
    ]
  ]);;

(* Subroutine version *)
let MLDSA_BUTTERFLY_SUBROUTINE_CORRECT = prove(
 `!pc stackpointer returnaddress l h zeta qinv.
     nonoverlapping (word pc, LENGTH mldsa_butterfly_instance_mc) (l, 32) /\
     nonoverlapping (word pc, LENGTH mldsa_butterfly_instance_mc) (h, 32) /\
     nonoverlapping (stackpointer, 8) (l, 32) /\
     nonoverlapping (stackpointer, 8) (h, 32)
     ==> ensures x86
          (\s. bytes_loaded s (word pc) mldsa_butterfly_instance_mc /\
               read RIP s = word pc /\
               read RSP s = stackpointer /\
               read (memory :> bytes64 stackpointer) s = returnaddress /\
               read YMM0 s = qinv /\
               read YMM1 s = zeta /\
               read YMM4 s = l /\
               read YMM8 s = h)
          (\s. read RIP s = returnaddress /\
               read RSP s = word_add stackpointer (word 8) /\
               let t = (h * zeta) mod mldsa_q in
               read YMM8 s = (l + t) mod mldsa_q /\
               read YMM4 s = (l - t) mod mldsa_q)
          (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [YMM4; YMM8; YMM12; YMM13; YMM14])`,
  X86_PROMOTE_RETURN_NOSTACK_TAC mldsa_butterfly_instance_mc MLDSA_BUTTERFLY_CORRECT
);;
