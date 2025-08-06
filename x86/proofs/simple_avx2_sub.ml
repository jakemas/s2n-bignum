(* ========================================================================= *)
(* Simple AVX2 vector subtraction proof for ML-DSA development              *)
(* ========================================================================= *)

needs "x86/proofs/base.ml";;

(**** print_literal_from_elf "x86/mldsa/simple_avx2_sub.o";;
 ****)

let simple_avx2_sub_mc = define_assert_from_elf "simple_avx2_sub_mc" "x86/mldsa/simple_avx2_sub.o"
[
  0xc5; 0x7d; 0xfa; 0xe1   (* VPSUBD (%_% ymm12) (%_% ymm0) (%_% ymm1) *)
];;

let SIMPLE_AVX2_SUB_EXEC = X86_MK_EXEC_RULE simple_avx2_sub_mc;;

(* ------------------------------------------------------------------------- *)
(* Proof.                                                                    *)
(* ------------------------------------------------------------------------- *)

(* Complete working proof with full type annotations for word_join and word_subword *)
let SIMPLE_AVX2_SUB_CORRECT = prove
 (`forall pc a b.
        ensures x86
             (\s. bytes_loaded s (word pc) simple_avx2_sub_mc /\
                  read RIP s = word pc /\
                  read YMM0 s = a /\
                  read YMM1 s = b)
             (\s. read RIP s = word (pc + LENGTH simple_avx2_sub_mc) /\
                  read YMM12 s = 
                  (word_join:(128)word->(128)word->(256)word)
                    ((word_join:(64)word->(64)word->(128)word)
                     ((word_join:(32)word->(32)word->(64)word)
                      (word_sub (word_subword a (224,32):(32)word) (word_subword b (224,32):(32)word))
                     (word_sub (word_subword a (192,32):(32)word) (word_subword b (192,32):(32)word)))
                    ((word_join:(32)word->(32)word->(64)word)
                     (word_sub (word_subword a (160,32):(32)word) (word_subword b (160,32):(32)word))
                    (word_sub (word_subword a (128,32):(32)word) (word_subword b (128,32):(32)word))))
                    ((word_join:(64)word->(64)word->(128)word)
                     ((word_join:(32)word->(32)word->(64)word)
                      (word_sub (word_subword a (96,32):(32)word) (word_subword b (96,32):(32)word))
                     (word_sub (word_subword a (64,32):(32)word) (word_subword b (64,32):(32)word)))
                    ((word_join:(32)word->(32)word->(64)word)
                     (word_sub (word_subword a (32,32):(32)word) (word_subword b (32,32):(32)word))
                    (word_sub (word_subword a (0,32):(32)word) (word_subword b (0,32):(32)word)))))
             (MAYCHANGE [RIP] ,, MAYCHANGE [ZMM12] ,, MAYCHANGE SOME_FLAGS)`,
  REWRITE_TAC [SOME_FLAGS; fst SIMPLE_AVX2_SUB_EXEC] THEN
  REPEAT STRIP_TAC THEN
  ENSURES_INIT_TAC "s0" THEN
  X86_STEPS_TAC SIMPLE_AVX2_SUB_EXEC (1--1) THEN
  ENSURES_FINAL_STATE_TAC THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[MAYCHANGE] THEN
  ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN
  TRY (REFL_TAC) THEN
  ALL_TAC);;

(* Interactive version with explicit type annotations *)
g `forall pc a b.
        ensures x86
             (\s. bytes_loaded s (word pc) simple_avx2_sub_mc /\
                  read RIP s = word pc /\
                  read YMM0 s = a /\
                  read YMM1 s = b)
             (\s. read RIP s = word (pc + LENGTH simple_avx2_sub_mc) /\
                  read YMM12 s = 
                  (word_join:(128)word->(128)word->(256)word)
                    ((word_join:(64)word->(64)word->(128)word)
                     ((word_join:(32)word->(32)word->(64)word)
                      (word_sub (word_subword a (224,32):(32)word) (word_subword b (224,32):(32)word))
                     (word_sub (word_subword a (192,32):(32)word) (word_subword b (192,32):(32)word)))
                    ((word_join:(32)word->(32)word->(64)word)
                     (word_sub (word_subword a (160,32):(32)word) (word_subword b (160,32):(32)word))
                    (word_sub (word_subword a (128,32):(32)word) (word_subword b (128,32):(32)word))))
                    ((word_join:(64)word->(64)word->(128)word)
                     ((word_join:(32)word->(32)word->(64)word)
                      (word_sub (word_subword a (96,32):(32)word) (word_subword b (96,32):(32)word))
                     (word_sub (word_subword a (64,32):(32)word) (word_subword b (64,32):(32)word)))
                    ((word_join:(32)word->(32)word->(64)word)
                     (word_sub (word_subword a (32,32):(32)word) (word_subword b (32,32):(32)word))
                    (word_sub (word_subword a (0,32):(32)word) (word_subword b (0,32):(32)word)))))
             (MAYCHANGE [RIP] ,, MAYCHANGE [ZMM12] ,, MAYCHANGE SOME_FLAGS)`;;

e (REWRITE_TAC [SOME_FLAGS; fst SIMPLE_AVX2_SUB_EXEC]);;
e (REPEAT STRIP_TAC);;
e (ENSURES_INIT_TAC "s0");;
e (X86_STEPS_TAC SIMPLE_AVX2_SUB_EXEC (1--1));;
e (ENSURES_FINAL_STATE_TAC);;
e (ASM_REWRITE_TAC[]);;
e (REWRITE_TAC[MAYCHANGE]);;
e (ASM_REWRITE_TAC[]);;
e (REPEAT CONJ_TAC);;
e (TRY (REFL_TAC));;
e (ALL_TAC);;
