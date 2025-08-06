(* ========================================================================= *)
(* ML-DSA Montgomery multiplication + first butterfly step (10 instructions) *)
(* ========================================================================= *)

needs "x86/proofs/base.ml";;
needs "x86/proofs/utils/mldsa.ml";;

let mldsa_mont_10_mc = define_assert_from_elf "mldsa_mont_10_mc" "x86/mldsa/mldsa_mont_9.o"
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
  0xc4; 0xc1; 0x7d; 0xfa; 0xe1
                           (* VPSUBD (%_% ymm12) (%_% ymm1) (%_% ymm8) *)
];;

let MLDSA_MONT_10_EXEC = X86_MK_EXEC_RULE mldsa_mont_10_mc;;

(* ------------------------------------------------------------------------- *)
(* Proof for 10-instruction sequence                                         *)
(* ------------------------------------------------------------------------- *)

let MLDSA_MONT_10_CORRECT = prove
 (`forall pc a b c d.
        ensures x86
             (\s. bytes_loaded s (word pc) mldsa_mont_10_mc /\
                  read RIP s = word pc /\
                  read YMM0 s = d /\
                  read YMM1 s = a /\
                  read YMM2 s = b /\
                  read YMM8 s = c)
             (\s. read RIP s = word (pc + LENGTH mldsa_mont_10_mc) /\
                  read YMM13 s = vpmuldq d (vpmuldq a c) /\
                  read YMM14 s = vpmuldq d (vpmuldq a (vmovshdup c)) /\
                  read YMM8 s = vpblendd (word 170) 
                                         (vmovshdup (vpmuldq b c))
                                         (vpmuldq b (vmovshdup c)) /\
                  read YMM12 s = vpsubd a (vpblendd (word 170) 
                                                    (vmovshdup (vpmuldq b c))
                                                    (vpmuldq b (vmovshdup c))))
             (MAYCHANGE [RIP] ,, MAYCHANGE [ZMM13; ZMM12; ZMM14; ZMM8] ,, MAYCHANGE SOME_FLAGS)`,
  REWRITE_TAC [SOME_FLAGS; fst MLDSA_MONT_10_EXEC] THEN
  REPEAT STRIP_TAC THEN
  ENSURES_INIT_TAC "s0" THEN
  
  MAP_EVERY (fun n -> X86_STEPS_TAC MLDSA_MONT_10_EXEC [n] THEN
                      X86_SIMD_SIMPLIFY_TAC [vpmuldq; vmovshdup; vpblendd])
            (1--9) THEN
  
  X86_STEPS_TAC MLDSA_MONT_10_EXEC [10] THEN
  X86_SIMD_SIMPLIFY_TAC [vpmuldq; vmovshdup; vpblendd; vpsubd] THEN
            
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[MAYCHANGE] THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM vpmuldq; GSYM vmovshdup; GSYM vpblendd; GSYM vpsubd] THEN
  REPEAT CONJ_TAC THEN TRY REFL_TAC);;


(* ------------------------------------------------------------------------- *)
(* Analysis of the 10-instruction sequence                                   *)
(* ------------------------------------------------------------------------- *)

(* Instructions 1-9: Montgomery multiplication (as proven before)
   - YMM13 = d * (a * c)
   - YMM14 = d * (a * shuffle(c))  
   - YMM8 = blend(shuffle(b * c), b * shuffle(c))
   
   Instruction 10: First butterfly step
   - YMM12 = a - YMM8  (vpsubd ymm12, ymm1, ymm8)
   
   This matches the butterfly macro pattern where:
   - ymm1 = a (low part)
   - ymm8 = high part (after blend)
   - The subtraction ymm12 = ymm1 - ymm8 is the first butterfly operation
*)
