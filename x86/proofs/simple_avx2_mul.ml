(* ========================================================================= *)
(* Simple AVX2 vector multiplcation proof for ML-DSA development             *)
(* ========================================================================= *)

needs "x86/proofs/base.ml";;

(**** print_literal_from_elf "x86/mldsa/simple_avx2_mul.o";;
****)

let simple_avx2_muldq_mc = define_assert_from_elf "simple_avx2_muldq_mc" "x86/mldsa/simple_avx2_mul.o"
[
  0xc4; 0x42; 0x75; 0x28; 0xe8   (* VPMULDQ (%_% ymm13) (%_% ymm1) (%_% ymm8) *)
];;

let SIMPLE_AVX2_MULDQ_EXEC = X86_MK_EXEC_RULE simple_avx2_muldq_mc;;

(* ------------------------------------------------------------------------- *)
(* Proof.                                                                    *)
(* ------------------------------------------------------------------------- *)

let SIMPLE_AVX2_MULDQ_CORRECT = prove
 (`forall pc a b.
        ensures x86
             (\s. bytes_loaded s (word pc) simple_avx2_muldq_mc /\
                  read RIP s = word pc /\
                  read YMM1 s = a /\
                  read YMM8 s = b)
             (\s. read RIP s = word (pc + LENGTH simple_avx2_muldq_mc) /\
                  read YMM13 s = 
                  (word_join:(128)word->(128)word->(256)word)
                    ((word_join:(64)word->(64)word->(128)word)
                     (word_mul (word_sx (word_subword (word_subword a (192,64):(64)word) (0,32):(32)word)) (word_sx (word_subword (word_subword b (192,64):(64)word) (0,32):(32)word)))
                     (word_mul (word_sx (word_subword (word_subword a (128,64):(64)word) (0,32):(32)word)) (word_sx (word_subword (word_subword b (128,64):(64)word) (0,32):(32)word))))
                    ((word_join:(64)word->(64)word->(128)word)
                     (word_mul (word_sx (word_subword (word_subword a (64,64):(64)word) (0,32):(32)word)) (word_sx (word_subword (word_subword b (64,64):(64)word) (0,32):(32)word)))
                     (word_mul (word_sx (word_subword (word_subword a (0,64):(64)word) (0,32):(32)word)) (word_sx (word_subword (word_subword b (0,64):(64)word) (0,32):(32)word)))))
             (MAYCHANGE [RIP] ,, MAYCHANGE [ZMM13] ,, MAYCHANGE SOME_FLAGS)`,
  REWRITE_TAC [SOME_FLAGS; fst SIMPLE_AVX2_MULDQ_EXEC] THEN
  REPEAT STRIP_TAC THEN
  ENSURES_INIT_TAC "s0" THEN
  X86_STEPS_TAC SIMPLE_AVX2_MULDQ_EXEC (1--1) THEN
  ENSURES_FINAL_STATE_TAC THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[MAYCHANGE] THEN
  ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN
  TRY (REFL_TAC) THEN
  ALL_TAC);;
