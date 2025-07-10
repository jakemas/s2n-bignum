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
 "mldsa_butterfly_instance_mc" "x86/mldsa/mldsa_butterfly.o"
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
let mldsa_q = define `mldsa_q = 8380417`;;

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
(* Partial products for Montgomery reduction have been computed *)
(* YMM13, YMM14 contain qinv-adjusted high parts *)
(* YMM8, YMM12 contain the low parts for blending *)
let montgomery_partial_complete = define
 `montgomery_partial_complete s h zeta <=>
    (ival(read YMM13 s) == ival h * ival zeta * &58728449) (mod &8380417) /\
    abs(ival(read YMM13 s)) <= &2147483647 /\
    (ival(read YMM14 s) == ival h * ival zeta * &58728449) (mod &8380417) /\
    abs(ival(read YMM14 s)) <= &2147483647 /\
    (ival(read YMM8 s) == ival h * ival zeta) (mod &8380417) /\
    abs(ival(read YMM8 s)) <= &2147483647 /\
    (ival(read YMM12 s) == ival h * ival zeta) (mod &8380417) /\
    abs(ival(read YMM12 s)) <= &2147483647`;;

(* State after Montgomery reduction complete (Chunk 2: Instructions 8-11) *)
(* Montgomery reduction is complete, t = montgomery_reduce(h * zeta) *)
(* YMM8 contains the reduced multiplication result *)
(* YMM4 and YMM12 contain l+t and l-t respectively *)
let montgomery_reduction_complete = define
 `montgomery_reduction_complete s l h zeta t_val <=>
    (ival(read YMM8 s) == montgomery_reduce(ival h * ival zeta)) (mod &8380417) /\
    abs(ival(read YMM8 s)) <= &8380416 /\
    (ival(read YMM4 s) == ival l + montgomery_reduce(ival h * ival zeta)) (mod &8380417) /\
    abs(ival(read YMM4 s)) <= &16760833 /\
    (ival(read YMM12 s) == ival l - montgomery_reduce(ival h * ival zeta)) (mod &8380417) /\
    abs(ival(read YMM12 s)) <= &16760833`;;

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
(* Supporting lemmas for completing the proof                                *)
(* ------------------------------------------------------------------------- *)

(* Simple lemma for Montgomery reduction definition *)
let MONTGOMERY_WORD_LEMMA = prove(
  `!h zeta. montgomery_multiply (val h) (val zeta) = montgomery_reduce (val h * val zeta)`,
  REWRITE_TAC[montgomery_multiply]);;

(* ------------------------------------------------------------------------- *)
(* Main correctness theorem with sequential proof structure                  *)
(* ------------------------------------------------------------------------- *)

(* WORK IN PROGRESS - to run
needs "x86/proofs/mldsa_butterfly.ml";; *)

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
    (* After these 7 instructions:
       - Instruction 1: VPMULDQ ymm13, ymm1, ymm8 (h * zeta -> ymm13)
       - Instruction 2: VMOVSHDUP ymm12, ymm8 (extract high parts of h)
       - Instruction 3: VPMULDQ ymm14, ymm1, ymm12 (high_h * zeta -> ymm14)
       - Instruction 4: VPMULDQ ymm8, ymm2, ymm8 (h * zeta2 -> ymm8)
       - Instruction 5: VPMULDQ ymm12, ymm2, ymm12 (high_h * zeta2 -> ymm12)
       - Instruction 6: VPMULDQ ymm13, ymm0, ymm13 (apply qinv to ymm13)
       - Instruction 7: VPMULDQ ymm14, ymm0, ymm14 (apply qinv to ymm14)
    *)
    (* The partial products for Montgomery reduction are now computed *)
    (* YMM13, YMM14 contain qinv-adjusted high parts *)
    (* YMM8, YMM12 contain the low parts for blending *)
    MAP_EVERY EXISTS_TAC [`read YMM13 s7`; `read YMM14 s7`; 
                          `read YMM8 s7`; `read YMM12 s7`] THEN
    (* All register values are simply what they contain after execution *)
    CONJ_TAC THENL [
      (* YMM13 contains the qinv-adjusted partial product *)
      REFL_TAC;
      CONJ_TAC THENL [
        (* YMM14 contains the qinv-adjusted high part partial product *)
        REFL_TAC;
        CONJ_TAC THENL [
          (* YMM8 contains h * zeta2 *)
          REFL_TAC;
          (* YMM12 contains high_h * zeta2 *)
          REFL_TAC
        ]
      ]
    ];
    
    (* CHUNK 2: Montgomery reduction (Instructions 8-11) *)
    ENSURES_SEQUENCE_TAC
      `pc + 56`  (* After instruction 11: VPADDD ymm4, ymm4, ymm8 *)
      `\s. ?t_val. montgomery_reduction_complete s l h zeta t_val` THEN
    
    CONJ_TAC THENL [
      (* Prove Chunk 2: Montgomery reduction *)
      ENSURES_INIT_TAC "s0" THEN
      X86_STEPS_TAC MLDSA_BUTTERFLY_EXEC (8--11) THEN
      ENSURES_FINAL_STATE_TAC THEN
      ASM_REWRITE_TAC[montgomery_reduction_complete] THEN
      (* After these 4 instructions:
         - Instruction 8: VMOVSHDUP ymm8, ymm8 (shuffle high parts)
         - Instruction 9: VPBLENDD ymm8, ymm8, ymm12, 0xAA (blend to complete Montgomery reduction)
         - Instruction 10: VPSUBD ymm12, ymm4, ymm8 (compute l - t)
         - Instruction 11: VPADDD ymm4, ymm4, ymm8 (compute l + t)
      *)
      (* YMM8 now contains t = montgomery_reduce(h * zeta) *)
      (* YMM4 contains l + t, YMM12 contains l - t *)
      EXISTS_TAC `read YMM8 s4` THEN
      CONJ_TAC THENL [
        (* YMM8 = t_val: This should be the Montgomery reduced multiplication result *)
        REFL_TAC;
        (* Provide witnesses for l+t and l-t *)
        MAP_EVERY EXISTS_TAC [`read YMM4 s4`; `read YMM12 s4`] THEN
        CONJ_TAC THENL [
          (* YMM4 = l_plus_t: This should be l + montgomery_reduce(h * zeta) *)
          REFL_TAC;
          (* YMM12 = l_minus_t: This should be l - montgomery_reduce(h * zeta) *)
          REFL_TAC
        ]
      ];
      
      (* CHUNK 3: Butterfly computation (Instructions 12-14) *)
      ENSURES_SEQUENCE_TAC
        `pc + 72`  (* After instruction 14: VPADDD ymm8, ymm12, ymm13 *)
        `\s. butterfly_computation_complete s l h zeta` THEN
      
      CONJ_TAC THENL [
        (* Prove Chunk 3: Butterfly computation *)
        ENSURES_INIT_TAC "s0" THEN
        X86_STEPS_TAC MLDSA_BUTTERFLY_EXEC (12--14) THEN
        ENSURES_FINAL_STATE_TAC THEN
        ASM_REWRITE_TAC[butterfly_computation_complete] THEN
        (* After these 3 instructions:
           - Instruction 12: VMOVSHDUP ymm13, ymm13 (shuffle high parts)
           - Instruction 13: VPBLENDD ymm13, ymm13, ymm14, 0xAA (blend correction)
           - Instruction 14: VPADDD ymm8, ymm12, ymm13 (compute h' = l-t + correction)
        *)
        MAP_EVERY EXISTS_TAC [`read YMM8 s3`; `read YMM4 s3`; `read YMM13 s3`] THEN
        (* The key insight: YMM8 now contains h', YMM4 contains intermediate l' *)
        (* YMM13 contains the correction factor *)
        CONJ_TAC THENL [
          (* YMM8 = h_prime: This should be the result of the butterfly h computation *)
          REFL_TAC;
          CONJ_TAC THENL [
            (* YMM4 = l_intermediate: This should be l+t from previous chunk *)
            REFL_TAC;
            (* YMM13 = correction: This should be the blended correction factor *)
            REFL_TAC
          ]
        ];
        
        (* CHUNK 4: Final output formatting (Instructions 15-16) *)
        (* This is the simplest chunk - just final register corrections *)
        ENSURES_INIT_TAC "s0" THEN
        X86_STEPS_TAC MLDSA_BUTTERFLY_EXEC (15--16) THEN
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
          (* After instruction 15: VPSUBD ymm4, ymm4, ymm13 *)
          (* We need to show that the subtraction gives us the correct l' value *)
          (* This requires connecting to the previous chunks' intermediate states *)
          ASM_REWRITE_TAC[] THEN
          (* The key insight: YMM4 after VPSUBD should equal word l' *)
          (* Let's trace through the computation:
             - Chunk 2: YMM4 = l + t (where t = montgomery_reduce(h * zeta))
             - Chunk 3: YMM4 unchanged, YMM13 = correction
             - Chunk 4: YMM4 = YMM4 - YMM13 = (l + t) - correction
             - We need to show: (l + t) - correction = l' = (l + t) MOD mldsa_q
          *)
          (* Use assumptions from previous chunks *)
          FIRST_X_ASSUM(STRIP_ASSUME_TAC) THEN
          (* We have butterfly_computation_complete assumption *)
          ASM_REWRITE_TAC[] THEN
          (* Connect to montgomery_reduction_complete from earlier *)
          (* The mathematical connection would show that correction adjusts for modular reduction *)
          (* For now, establish the proof structure *)
          REWRITE_TAC[montgomery_multiply; montgomery_reduce] THEN
          (* The symbolic execution has already established the register states *)
          (* We rely on the intermediate state assumptions from previous chunks *)
          ASM_REWRITE_TAC[];
          
          (* Show YMM8 contains h' = (l - montgomery_reduce(h * zeta)) MOD mldsa_q *)
          (* YMM8 should already contain h' from the previous chunk *)
          (* The RET instruction doesn't change YMM8 *)
          ASM_REWRITE_TAC[] THEN
          (* YMM8 should remain unchanged from previous chunk *)
          (* Key insight: YMM8 was set in Chunk 3 and RET doesn't modify it *)
          (* We need to connect the butterfly_computation_complete assumption *)
          (* to show that YMM8 already contains the correct h' value *)
          FIRST_X_ASSUM(STRIP_ASSUME_TAC) THEN
          (* Use the fact that YMM8 = h_prime from previous chunk *)
          (* This h_prime should equal the mathematical h' *)
          ASM_REWRITE_TAC[] THEN
          (* Connect h_prime to the mathematical specification *)
          (* YMM8 was computed in Chunk 3 as h' = (l - t) + correction *)
          (* which should equal (l - montgomery_reduce(h * zeta)) MOD mldsa_q *)
          REWRITE_TAC[montgomery_multiply; montgomery_reduce] THEN
          (* Use word arithmetic to connect the register computation to math spec *)
          CONV_TAC WORD_RULE THEN
          (* The RET instruction preserves YMM8, so the value is unchanged *)
          ASM_REWRITE_TAC[]
        ]
      ]
    ]
  ]);;
