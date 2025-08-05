(* ========================================================================= *)
(* ML-DSA Montgomery multiplication - 3 instruction sequence                 *)
(* vpmuldq ymm13, ymm1, ymm8                                                 *)
(* vmovshdup ymm12, ymm8                                                     *)
(* vpmuldq ymm14, ymm1, ymm12                                                *)
(* ========================================================================= *)

needs "x86/proofs/base.ml";;

(**** print_literal_from_elf "x86/mldsa/mldsa_mont_2.o";;
 ****)

let mldsa_mont_3instr_mc = define_assert_from_elf "mldsa_mont_3instr_mc" "x86/mldsa/mldsa_mont_2.o"
[
  0xc4; 0x42; 0x75; 0x28; 0xe8;
                           (* VPMULDQ (%_% ymm13) (%_% ymm1) (%_% ymm8) *)
  0xc4; 0x41; 0x7e; 0x16; 0xe0;
                           (* VMOVSHDUP (%_% ymm12) (%_% ymm8) *)
  0xc4; 0x42; 0x75; 0x28; 0xf4
                           (* VPMULDQ (%_% ymm14) (%_% ymm1) (%_% ymm12) *)
];;

let MLDSA_MONT_3INSTR_EXEC = X86_MK_EXEC_RULE mldsa_mont_3instr_mc;;

(* ------------------------------------------------------------------------- *)
(* Proof.                                                                    *)
(* ------------------------------------------------------------------------- *)


(* basic flow *)

let MLDSA_MONT_3INSTR_CORRECT = prove
 (`forall pc a b.
        ensures x86
             (\s. bytes_loaded s (word pc) mldsa_mont_3instr_mc /\
                  read RIP s = word pc /\
                  read YMM1 s = a /\
                  read YMM8 s = b)
             (\s. read RIP s = word (pc + LENGTH mldsa_mont_3instr_mc))
             (MAYCHANGE [RIP] ,, MAYCHANGE [ZMM13; ZMM12; ZMM14] ,, MAYCHANGE SOME_FLAGS)`,
  REWRITE_TAC [SOME_FLAGS; fst MLDSA_MONT_3INSTR_EXEC] THEN
  REPEAT STRIP_TAC THEN
  ENSURES_INIT_TAC "s0" THEN
  X86_STEPS_TAC MLDSA_MONT_3INSTR_EXEC (1--3) THEN
  ENSURES_FINAL_STATE_TAC THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[MAYCHANGE] THEN
  ASM_REWRITE_TAC[]);;

(* functional proof *)

let MLDSA_MONT_3INSTR_FUNCTIONAL = prove
 (`forall pc a b.
        ensures x86
             (\s. bytes_loaded s (word pc) mldsa_mont_3instr_mc /\
                  read RIP s = word pc /\
                  read YMM1 s = a /\
                  read YMM8 s = b)
             (\s. read RIP s = word (pc + LENGTH mldsa_mont_3instr_mc) /\
                  read YMM13 s = 
                  (word_join:(128)word->(128)word->(256)word)
                    ((word_join:(64)word->(64)word->(128)word)
                     (word_mul (word_sx (word_subword (word_subword a (192,64):(64)word) (0,32):(32)word)) 
                               (word_sx (word_subword (word_subword b (192,64):(64)word) (0,32):(32)word)))
                     (word_mul (word_sx (word_subword (word_subword a (128,64):(64)word) (0,32):(32)word)) 
                               (word_sx (word_subword (word_subword b (128,64):(64)word) (0,32):(32)word))))
                    ((word_join:(64)word->(64)word->(128)word)
                     (word_mul (word_sx (word_subword (word_subword a (64,64):(64)word) (0,32):(32)word)) 
                               (word_sx (word_subword (word_subword b (64,64):(64)word) (0,32):(32)word)))
                     (word_mul (word_sx (word_subword (word_subword a (0,64):(64)word) (0,32):(32)word)) 
                               (word_sx (word_subword (word_subword b (0,64):(64)word) (0,32):(32)word)))) /\
                  read YMM12 s = 
                  (word_join:(128)word->(128)word->(256)word)
                    ((word_join:(64)word->(64)word->(128)word)
                     ((word_join:(32)word->(32)word->(64)word) (word_subword b (224,32):(32)word) (word_subword b (224,32):(32)word))
                     ((word_join:(32)word->(32)word->(64)word) (word_subword b (160,32):(32)word) (word_subword b (160,32):(32)word)))
                    ((word_join:(64)word->(64)word->(128)word)
                     ((word_join:(32)word->(32)word->(64)word) (word_subword b (96,32):(32)word) (word_subword b (96,32):(32)word))
                     ((word_join:(32)word->(32)word->(64)word) (word_subword b (32,32):(32)word) (word_subword b (32,32):(32)word))) /\
                  read YMM14 s = 
                  (word_join:(128)word->(128)word->(256)word)
                    ((word_join:(64)word->(64)word->(128)word)
                     (word_mul (word_sx (word_subword (word_subword a (192,64):(64)word) (0,32):(32)word)) 
                               (word_sx (word_subword (word_subword 
                                 ((word_join:(128)word->(128)word->(256)word)
                                   ((word_join:(64)word->(64)word->(128)word)
                                    ((word_join:(32)word->(32)word->(64)word) (word_subword b (224,32):(32)word) (word_subword b (224,32):(32)word))
                                    ((word_join:(32)word->(32)word->(64)word) (word_subword b (160,32):(32)word) (word_subword b (160,32):(32)word)))
                                   ((word_join:(64)word->(64)word->(128)word)
                                    ((word_join:(32)word->(32)word->(64)word) (word_subword b (96,32):(32)word) (word_subword b (96,32):(32)word))
                                    ((word_join:(32)word->(32)word->(64)word) (word_subword b (32,32):(32)word) (word_subword b (32,32):(32)word))))
                                 (192,64):(64)word) (0,32):(32)word)))
                     (word_mul (word_sx (word_subword (word_subword a (128,64):(64)word) (0,32):(32)word)) 
                               (word_sx (word_subword (word_subword 
                                 ((word_join:(128)word->(128)word->(256)word)
                                   ((word_join:(64)word->(64)word->(128)word)
                                    ((word_join:(32)word->(32)word->(64)word) (word_subword b (224,32):(32)word) (word_subword b (224,32):(32)word))
                                    ((word_join:(32)word->(32)word->(64)word) (word_subword b (160,32):(32)word) (word_subword b (160,32):(32)word)))
                                   ((word_join:(64)word->(64)word->(128)word)
                                    ((word_join:(32)word->(32)word->(64)word) (word_subword b (96,32):(32)word) (word_subword b (96,32):(32)word))
                                    ((word_join:(32)word->(32)word->(64)word) (word_subword b (32,32):(32)word) (word_subword b (32,32):(32)word))))
                                 (128,64):(64)word) (0,32):(32)word))))
                    ((word_join:(64)word->(64)word->(128)word)
                     (word_mul (word_sx (word_subword (word_subword a (64,64):(64)word) (0,32):(32)word)) 
                               (word_sx (word_subword (word_subword 
                                 ((word_join:(128)word->(128)word->(256)word)
                                   ((word_join:(64)word->(64)word->(128)word)
                                    ((word_join:(32)word->(32)word->(64)word) (word_subword b (224,32):(32)word) (word_subword b (224,32):(32)word))
                                    ((word_join:(32)word->(32)word->(64)word) (word_subword b (160,32):(32)word) (word_subword b (160,32):(32)word)))
                                   ((word_join:(64)word->(64)word->(128)word)
                                    ((word_join:(32)word->(32)word->(64)word) (word_subword b (96,32):(32)word) (word_subword b (96,32):(32)word))
                                    ((word_join:(32)word->(32)word->(64)word) (word_subword b (32,32):(32)word) (word_subword b (32,32):(32)word))))
                                 (64,64):(64)word) (0,32):(32)word)))
                     (word_mul (word_sx (word_subword (word_subword a (0,64):(64)word) (0,32):(32)word)) 
                               (word_sx (word_subword (word_subword 
                                 ((word_join:(128)word->(128)word->(256)word)
                                   ((word_join:(64)word->(64)word->(128)word)
                                    ((word_join:(32)word->(32)word->(64)word) (word_subword b (224,32):(32)word) (word_subword b (224,32):(32)word))
                                    ((word_join:(32)word->(32)word->(64)word) (word_subword b (160,32):(32)word) (word_subword b (160,32):(32)word)))
                                   ((word_join:(64)word->(64)word->(128)word)
                                    ((word_join:(32)word->(32)word->(64)word) (word_subword b (96,32):(32)word) (word_subword b (96,32):(32)word))
                                    ((word_join:(32)word->(32)word->(64)word) (word_subword b (32,32):(32)word) (word_subword b (32,32):(32)word))))
                                 (0,64):(64)word) (0,32):(32)word)))))
             (MAYCHANGE [RIP] ,, MAYCHANGE [ZMM13; ZMM12; ZMM14] ,, MAYCHANGE SOME_FLAGS)`,
  REWRITE_TAC [SOME_FLAGS; fst MLDSA_MONT_3INSTR_EXEC] THEN
  REPEAT STRIP_TAC THEN
  ENSURES_INIT_TAC "s0" THEN
  X86_STEPS_TAC MLDSA_MONT_3INSTR_EXEC (1--3) THEN
  ENSURES_FINAL_STATE_TAC THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[MAYCHANGE] THEN
  ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN
  TRY (REFL_TAC) THEN
  ALL_TAC);;
