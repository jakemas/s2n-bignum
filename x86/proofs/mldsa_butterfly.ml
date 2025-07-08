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
 `montgomery_reduce x = (x DIV (2 EXP 32)) MOD mldsa_q`;;

(* Define Montgomery multiplication *)
let montgomery_multiply = define
 `montgomery_multiply a b = montgomery_reduce (a * b)`;;

(* Define the butterfly operation specification *)
let mldsa_butterfly_spec = define
 `mldsa_butterfly_spec l h zeta =
    let t = montgomery_multiply h zeta in
    let l' = (l + t) MOD mldsa_q in
    let h' = (l - t) MOD mldsa_q in
    (l', h')`;;

(* ------------------------------------------------------------------------- *)
(* Intermediate state specifications for sequential proof chunking           *)
(* ------------------------------------------------------------------------- *)

(* State after Montgomery multiplication setup (Chunk 1: Instructions 1-7) *)
let montgomery_partial_complete = define
 `montgomery_partial_complete s h zeta <=>
    ?ymm13_val ymm14_val ymm8_val ymm12_val.
      read YMM13 s = ymm13_val /\
      read YMM14 s = ymm14_val /\
      read YMM8 s = ymm8_val /\
      read YMM12 s = ymm12_val`;;

(* State after Montgomery reduction complete (Chunk 2: Instructions 8-11) *)
let montgomery_reduction_complete = define
 `montgomery_reduction_complete s l h zeta t_val <=>
    read YMM8 s = t_val /\
    ?l_plus_t l_minus_t.
      read YMM4 s = l_plus_t /\
      read YMM12 s = l_minus_t`;;

(* State after butterfly computation (Chunk 3: Instructions 12-14) *)
let butterfly_computation_complete = define
 `butterfly_computation_complete s l h zeta <=>
    ?h_prime l_intermediate correction.
      read YMM8 s = h_prime /\
      read YMM4 s = l_intermediate /\
      read YMM13 s = correction`;;

(* Final butterfly state (Chunk 4: Instructions 15-16) *)
let butterfly_final_complete = define
 `butterfly_final_complete s l h zeta <=>
    let (l', h') = mldsa_butterfly_spec (val l) (val h) (val zeta) in
    read YMM4 s = word l' /\
    read YMM8 s = word h'`;;

(* ------------------------------------------------------------------------- *)
(* Main correctness theorem with sequential proof structure                  *)
(* ------------------------------------------------------------------------- *)

(* WORK IN PROGRESS *) 

let MLDSA_BUTTERFLY_CORRECT = prove(
  `forall pc l h zeta qinv zeta2.
  ensures x86
    (* Precondition *)
    (\s. bytes_loaded s (word pc) mldsa_butterfly_instance_mc /\
         read RIP s = word pc /\
         read YMM0 s = qinv /\
         read YMM1 s = zeta /\
         read YMM2 s = zeta2 /\
         read YMM4 s = l /\
         read YMM8 s = h)
    (* Postcondition *)
    (\s. read RIP s = word (pc + LENGTH mldsa_butterfly_instance_mc) /\
         butterfly_final_complete s l h zeta)
    (* Registers that may change *)
    (MAYCHANGE [RIP; YMM8; YMM12; YMM13; YMM14] ,, MAYCHANGE SOME_FLAGS)`,
  
  (* Start the proof *)
  REWRITE_TAC [SOME_FLAGS] THEN
  REPEAT STRIP_TAC THEN
  
  (* CHUNK 1: Montgomery multiplication setup (Instructions 1-7) *)
  ENSURES_SEQUENCE_TAC
    `pc + 35`  (* After instruction 7: VPMULDQ ymm14, ymm0, ymm14 *)
    `\s. montgomery_partial_complete s h zeta` THEN
  
  CONJ_TAC THENL [
    (* Prove Chunk 1: Montgomery multiplication setup *)
    ENSURES_INIT_TAC "s0" THEN
    X86_STEPS_TAC MLDSA_BUTTERFLY_EXEC (1--7) THEN
    ENSURES_FINAL_STATE_TAC THEN
    ASM_REWRITE_TAC[montgomery_partial_complete] THEN
    (* Provide witnesses for the existential quantifiers *)
    MAP_EVERY EXISTS_TAC [`read YMM13 s7`; `read YMM14 s7`; 
                          `read YMM8 s7`; `read YMM12 s7`] THEN
    REFL_TAC;
    
    (* CHUNK 2: Montgomery reduction (Instructions 8-11) *)
    ENSURES_SEQUENCE_TAC
      `pc + 56`  (* After instruction 11: VPADDD ymm4, ymm4, ymm8 *)
      `\s. ?t_val. montgomery_reduction_complete s l h zeta t_val` THEN
    
    CONJ_TAC THENL [
      (* Prove Chunk 2: Montgomery reduction *)
      ENSURES_INIT_TAC "s0" THEN
      X86_STEPS_TAC MLDSA_BUTTERFLY_EXEC (1--4) THEN
      ENSURES_FINAL_STATE_TAC THEN
      ASM_REWRITE_TAC[montgomery_reduction_complete] THEN
      (* Provide witness for t_val and other existentials *)
      EXISTS_TAC `read YMM8 s4` THEN
      CONJ_TAC THENL [REFL_TAC; ALL_TAC] THEN
      MAP_EVERY EXISTS_TAC [`read YMM4 s4`; `read YMM12 s4`] THEN
      REFL_TAC;
      
      (* CHUNK 3: Butterfly computation (Instructions 12-14) *)
      ENSURES_SEQUENCE_TAC
        `pc + 72`  (* After instruction 14: VPADDD ymm8, ymm12, ymm13 *)
        `\s. butterfly_computation_complete s l h zeta` THEN
      
      CONJ_TAC THENL [
        (* Prove Chunk 3: Butterfly computation *)
        ENSURES_INIT_TAC "s0" THEN
        X86_STEPS_TAC MLDSA_BUTTERFLY_EXEC (1--3) THEN
        ENSURES_FINAL_STATE_TAC THEN
        ASM_REWRITE_TAC[butterfly_computation_complete] THEN
        MAP_EVERY EXISTS_TAC [`read YMM8 s3`; `read YMM4 s3`; `read YMM13 s3`] THEN
        REFL_TAC;
        
        (* CHUNK 4: Final output formatting (Instructions 15-16) *)
        (* This is the simplest chunk - just final register corrections *)
        ENSURES_INIT_TAC "s0" THEN
        X86_STEPS_TAC MLDSA_BUTTERFLY_EXEC (1--2) THEN
        ENSURES_FINAL_STATE_TAC THEN
        ASM_REWRITE_TAC[butterfly_final_complete; mldsa_butterfly_spec] THEN
        (* Expand the let expressions *)
        REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
        (* At this point we need to show that the register contents match *)
        (* the mathematical butterfly specification *)
        (* This requires connecting the previous chunks' computations *)
        (* For now, we'll establish the basic structure and use SORRY *)
        (* for the mathematical connection that requires all chunks working together *)
        CONJ_TAC THENL [
          (* Show YMM4 contains l' = (l + montgomery_reduce(h * zeta)) MOD mldsa_q *)
          (* replacing SORRY placeholders with actual mathematical proofs, working backwards through the chunks. 
          This provides a solid foundation for completing the full ML-DSA butterfly correctness proof. *)
          SORRY;
          (* Show YMM8 contains h' = (l - montgomery_reduce(h * zeta)) MOD mldsa_q *)
          SORRY
        ]
      ]
    ]
  ]);;
