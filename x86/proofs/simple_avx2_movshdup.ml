(* ========================================================================= *)
(* Simple AVX2 vector movshdup proof for ML-DSA development                  *)
(* ========================================================================= *)

needs "x86/proofs/base.ml";;

(**** print_literal_from_elf "x86/mldsa/simple_avx2_movshdup.o";;
 ****)

print_literal_from_elf "x86/mldsa/simple_avx2_movshdup.o";;

let simple_avx2_movshdup_mc = define_assert_from_elf "simple_avx2_movshdup_mc" "x86/mldsa/simple_avx2_movshdup.o"
[
  0xc4; 0x41; 0x7e; 0x16; 0xe0
                           (* VMOVSHDUP (%_% ymm12) (%_% ymm8) *)
];;

let SIMPLE_AVX2_MOVSHDUP_EXEC = X86_MK_EXEC_RULE simple_avx2_movshdup_mc;;

let SIMPLE_AVX2_MOVSHDUP_CORRECT = prove
 (`forall pc a.
        ensures x86
             (\s. bytes_loaded s (word pc) simple_avx2_movshdup_mc /\
                  read RIP s = word pc /\
                  read YMM8 s = a)
             (\s. read RIP s = word (pc + LENGTH simple_avx2_movshdup_mc) /\
                  read YMM12 s = 
                  (word_join:(128)word->(128)word->(256)word)
                    ((word_join:(64)word->(64)word->(128)word)
                     ((word_join:(32)word->(32)word->(64)word)
                      (word_subword a (224,32):(32)word) (word_subword a (224,32):(32)word))
                     ((word_join:(32)word->(32)word->(64)word)
                      (word_subword a (160,32):(32)word) (word_subword a (160,32):(32)word)))
                    ((word_join:(64)word->(64)word->(128)word)
                     ((word_join:(32)word->(32)word->(64)word)
                      (word_subword a (96,32):(32)word) (word_subword a (96,32):(32)word))
                     ((word_join:(32)word->(32)word->(64)word)
                      (word_subword a (32,32):(32)word) (word_subword a (32,32):(32)word))))
             (MAYCHANGE [RIP] ,, MAYCHANGE [ZMM12] ,, MAYCHANGE SOME_FLAGS)`,
  REWRITE_TAC [SOME_FLAGS; fst SIMPLE_AVX2_MOVSHDUP_EXEC] THEN
  REPEAT STRIP_TAC THEN
  ENSURES_INIT_TAC "s0" THEN
  X86_STEPS_TAC SIMPLE_AVX2_MOVSHDUP_EXEC (1--1) THEN
  ENSURES_FINAL_STATE_TAC THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[MAYCHANGE] THEN
  ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN
  TRY (REFL_TAC) THEN
  ALL_TAC);;