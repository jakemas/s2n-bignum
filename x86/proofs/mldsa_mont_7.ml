(* ========================================================================= *)
(* ML-DSA Montgomery multiplication - 8 instruction sequence                 *)
(* Using the successful explicit type annotation pattern                     *)
(* ========================================================================= *)

needs "x86/proofs/base.ml";;

(**** print_literal_from_elf "x86/mldsa/mldsa_mont_7.o";;
 ****)

let mldsa_mont_8instr_mc = define_assert_from_elf "mldsa_mont_8instr_mc" "x86/mldsa/mldsa_mont_7.o"
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
  0xc4; 0x41; 0x7e; 0x16; 0xc0
                           (* VMOVSHDUP (%_% ymm8) (%_% ymm8) *)
];;

let MLDSA_MONT_8INSTR_EXEC = X86_MK_EXEC_RULE mldsa_mont_8instr_mc;;

(* ------------------------------------------------------------------------- *)
(* Basic execution proof                                                     *)
(* ------------------------------------------------------------------------- *)

let MLDSA_MONT_8INSTR_CORRECT = prove
 (`forall pc a b c d.
        ensures x86
             (\s. bytes_loaded s (word pc) mldsa_mont_8instr_mc /\
                  read RIP s = word pc /\
                  read YMM0 s = d /\
                  read YMM1 s = a /\
                  read YMM2 s = b /\
                  read YMM8 s = c)
             (\s. read RIP s = word (pc + LENGTH mldsa_mont_8instr_mc))
             (MAYCHANGE [RIP] ,, MAYCHANGE [ZMM13; ZMM12; ZMM14; ZMM8] ,, MAYCHANGE SOME_FLAGS)`,
  REWRITE_TAC [SOME_FLAGS; fst MLDSA_MONT_8INSTR_EXEC] THEN
  REPEAT STRIP_TAC THEN
  ENSURES_INIT_TAC "s0" THEN
  X86_STEPS_TAC MLDSA_MONT_8INSTR_EXEC (1--8) THEN
  ENSURES_FINAL_STATE_TAC THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[MAYCHANGE] THEN
  ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Functional correctness proof with explicit type annotations               *)
(* ------------------------------------------------------------------------- *)

let MLDSA_MONT_8INSTR_FUNCTIONAL = prove
 (`forall pc a b c d.
        ensures x86
             (\s. bytes_loaded s (word pc) mldsa_mont_8instr_mc /\
                  read RIP s = word pc /\
                  read YMM0 s = d /\
                  read YMM1 s = a /\
                  read YMM2 s = b /\
                  read YMM8 s = c)
             (\s. read RIP s = word (pc + LENGTH mldsa_mont_8instr_mc) /\
                  read YMM13 s = 
                  (word_join:(128)word->(128)word->(256)word)
                    ((word_join:(64)word->(64)word->(128)word)
                     (word_mul (word_sx (word_subword (word_subword d (192,64):(64)word) (0,32):(32)word)) 
                               (word_sx (word_subword (word_subword 
                                 ((word_join:(128)word->(128)word->(256)word)
                                   ((word_join:(64)word->(64)word->(128)word)
                                    (word_mul (word_sx (word_subword (word_subword a (192,64):(64)word) (0,32):(32)word)) 
                                              (word_sx (word_subword (word_subword c (192,64):(64)word) (0,32):(32)word)))
                                    (word_mul (word_sx (word_subword (word_subword a (128,64):(64)word) (0,32):(32)word)) 
                                              (word_sx (word_subword (word_subword c (128,64):(64)word) (0,32):(32)word))))
                                   ((word_join:(64)word->(64)word->(128)word)
                                    (word_mul (word_sx (word_subword (word_subword a (64,64):(64)word) (0,32):(32)word)) 
                                              (word_sx (word_subword (word_subword c (64,64):(64)word) (0,32):(32)word)))
                                    (word_mul (word_sx (word_subword (word_subword a (0,64):(64)word) (0,32):(32)word)) 
                                              (word_sx (word_subword (word_subword c (0,64):(64)word) (0,32):(32)word)))))
                                 (192,64):(64)word) (0,32):(32)word)))
                     (word_mul (word_sx (word_subword (word_subword d (128,64):(64)word) (0,32):(32)word)) 
                               (word_sx (word_subword (word_subword 
                                 ((word_join:(128)word->(128)word->(256)word)
                                   ((word_join:(64)word->(64)word->(128)word)
                                    (word_mul (word_sx (word_subword (word_subword a (192,64):(64)word) (0,32):(32)word)) 
                                              (word_sx (word_subword (word_subword c (192,64):(64)word) (0,32):(32)word)))
                                    (word_mul (word_sx (word_subword (word_subword a (128,64):(64)word) (0,32):(32)word)) 
                                              (word_sx (word_subword (word_subword c (128,64):(64)word) (0,32):(32)word))))
                                   ((word_join:(64)word->(64)word->(128)word)
                                    (word_mul (word_sx (word_subword (word_subword a (64,64):(64)word) (0,32):(32)word)) 
                                              (word_sx (word_subword (word_subword c (64,64):(64)word) (0,32):(32)word)))
                                    (word_mul (word_sx (word_subword (word_subword a (0,64):(64)word) (0,32):(32)word)) 
                                              (word_sx (word_subword (word_subword c (0,64):(64)word) (0,32):(32)word)))))
                                 (128,64):(64)word) (0,32):(32)word))))
                    ((word_join:(64)word->(64)word->(128)word)
                     (word_mul (word_sx (word_subword (word_subword d (64,64):(64)word) (0,32):(32)word)) 
                               (word_sx (word_subword (word_subword 
                                 ((word_join:(128)word->(128)word->(256)word)
                                   ((word_join:(64)word->(64)word->(128)word)
                                    (word_mul (word_sx (word_subword (word_subword a (192,64):(64)word) (0,32):(32)word)) 
                                              (word_sx (word_subword (word_subword c (192,64):(64)word) (0,32):(32)word)))
                                    (word_mul (word_sx (word_subword (word_subword a (128,64):(64)word) (0,32):(32)word)) 
                                              (word_sx (word_subword (word_subword c (128,64):(64)word) (0,32):(32)word))))
                                   ((word_join:(64)word->(64)word->(128)word)
                                    (word_mul (word_sx (word_subword (word_subword a (64,64):(64)word) (0,32):(32)word)) 
                                              (word_sx (word_subword (word_subword c (64,64):(64)word) (0,32):(32)word)))
                                    (word_mul (word_sx (word_subword (word_subword a (0,64):(64)word) (0,32):(32)word)) 
                                              (word_sx (word_subword (word_subword c (0,64):(64)word) (0,32):(32)word)))))
                                 (64,64):(64)word) (0,32):(32)word)))
                     (word_mul (word_sx (word_subword (word_subword d (0,64):(64)word) (0,32):(32)word)) 
                               (word_sx (word_subword (word_subword 
                                 ((word_join:(128)word->(128)word->(256)word)
                                   ((word_join:(64)word->(64)word->(128)word)
                                    (word_mul (word_sx (word_subword (word_subword a (192,64):(64)word) (0,32):(32)word)) 
                                              (word_sx (word_subword (word_subword c (192,64):(64)word) (0,32):(32)word)))
                                    (word_mul (word_sx (word_subword (word_subword a (128,64):(64)word) (0,32):(32)word)) 
                                              (word_sx (word_subword (word_subword c (128,64):(64)word) (0,32):(32)word))))
                                   ((word_join:(64)word->(64)word->(128)word)
                                    (word_mul (word_sx (word_subword (word_subword a (64,64):(64)word) (0,32):(32)word)) 
                                              (word_sx (word_subword (word_subword c (64,64):(64)word) (0,32):(32)word)))
                                    (word_mul (word_sx (word_subword (word_subword a (0,64):(64)word) (0,32):(32)word)) 
                                              (word_sx (word_subword (word_subword c (0,64):(64)word) (0,32):(32)word)))))
                                 (0,64):(64)word) (0,32):(32)word)))) /\
                  read YMM14 s = 
                  (word_join:(128)word->(128)word->(256)word)
                    ((word_join:(64)word->(64)word->(128)word)
                     (word_mul (word_sx (word_subword (word_subword d (192,64):(64)word) (0,32):(32)word)) 
                               (word_sx (word_subword (word_subword 
                                 ((word_join:(128)word->(128)word->(256)word)
                                   ((word_join:(64)word->(64)word->(128)word)
                                    (word_mul (word_sx (word_subword (word_subword a (192,64):(64)word) (0,32):(32)word)) 
                                              (word_sx (word_subword (word_subword 
                                                ((word_join:(128)word->(128)word->(256)word)
                                                  ((word_join:(64)word->(64)word->(128)word)
                                                   ((word_join:(32)word->(32)word->(64)word) (word_subword c (224,32):(32)word) (word_subword c (224,32):(32)word))
                                                   ((word_join:(32)word->(32)word->(64)word) (word_subword c (160,32):(32)word) (word_subword c (160,32):(32)word)))
                                                  ((word_join:(64)word->(64)word->(128)word)
                                                   ((word_join:(32)word->(32)word->(64)word) (word_subword c (96,32):(32)word) (word_subword c (96,32):(32)word))
                                                   ((word_join:(32)word->(32)word->(64)word) (word_subword c (32,32):(32)word) (word_subword c (32,32):(32)word))))
                                                (192,64):(64)word) (0,32):(32)word)))
                                    (word_mul (word_sx (word_subword (word_subword a (128,64):(64)word) (0,32):(32)word)) 
                                              (word_sx (word_subword (word_subword 
                                                ((word_join:(128)word->(128)word->(256)word)
                                                  ((word_join:(64)word->(64)word->(128)word)
                                                   ((word_join:(32)word->(32)word->(64)word) (word_subword c (224,32):(32)word) (word_subword c (224,32):(32)word))
                                                   ((word_join:(32)word->(32)word->(64)word) (word_subword c (160,32):(32)word) (word_subword c (160,32):(32)word)))
                                                  ((word_join:(64)word->(64)word->(128)word)
                                                   ((word_join:(32)word->(32)word->(64)word) (word_subword c (96,32):(32)word) (word_subword c (96,32):(32)word))
                                                   ((word_join:(32)word->(32)word->(64)word) (word_subword c (32,32):(32)word) (word_subword c (32,32):(32)word))))
                                                (128,64):(64)word) (0,32):(32)word))))
                                   ((word_join:(64)word->(64)word->(128)word)
                                    (word_mul (word_sx (word_subword (word_subword a (64,64):(64)word) (0,32):(32)word)) 
                                              (word_sx (word_subword (word_subword 
                                                ((word_join:(128)word->(128)word->(256)word)
                                                  ((word_join:(64)word->(64)word->(128)word)
                                                   ((word_join:(32)word->(32)word->(64)word) (word_subword c (224,32):(32)word) (word_subword c (224,32):(32)word))
                                                   ((word_join:(32)word->(32)word->(64)word) (word_subword c (160,32):(32)word) (word_subword c (160,32):(32)word)))
                                                  ((word_join:(64)word->(64)word->(128)word)
                                                   ((word_join:(32)word->(32)word->(64)word) (word_subword c (96,32):(32)word) (word_subword c (96,32):(32)word))
                                                   ((word_join:(32)word->(32)word->(64)word) (word_subword c (32,32):(32)word) (word_subword c (32,32):(32)word))))
                                                (64,64):(64)word) (0,32):(32)word)))
                                    (word_mul (word_sx (word_subword (word_subword a (0,64):(64)word) (0,32):(32)word)) 
                                              (word_sx (word_subword (word_subword 
                                                ((word_join:(128)word->(128)word->(256)word)
                                                  ((word_join:(64)word->(64)word->(128)word)
                                                   ((word_join:(32)word->(32)word->(64)word) (word_subword c (224,32):(32)word) (word_subword c (224,32):(32)word))
                                                   ((word_join:(32)word->(32)word->(64)word) (word_subword c (160,32):(32)word) (word_subword c (160,32):(32)word)))
                                                  ((word_join:(64)word->(64)word->(128)word)
                                                   ((word_join:(32)word->(32)word->(64)word) (word_subword c (96,32):(32)word) (word_subword c (96,32):(32)word))
                                                   ((word_join:(32)word->(32)word->(64)word) (word_subword c (32,32):(32)word) (word_subword c (32,32):(32)word))))
                                                (0,64):(64)word) (0,32):(32)word)))))
                                 (192,64):(64)word) (0,32):(32)word)))
                     (word_mul (word_sx (word_subword (word_subword d (128,64):(64)word) (0,32):(32)word)) 
                               (word_sx (word_subword (word_subword 
                                 ((word_join:(128)word->(128)word->(256)word)
                                   ((word_join:(64)word->(64)word->(128)word)
                                    (word_mul (word_sx (word_subword (word_subword a (192,64):(64)word) (0,32):(32)word)) 
                                              (word_sx (word_subword (word_subword 
                                                ((word_join:(128)word->(128)word->(256)word)
                                                  ((word_join:(64)word->(64)word->(128)word)
                                                   ((word_join:(32)word->(32)word->(64)word) (word_subword c (224,32):(32)word) (word_subword c (224,32):(32)word))
                                                   ((word_join:(32)word->(32)word->(64)word) (word_subword c (160,32):(32)word) (word_subword c (160,32):(32)word)))
                                                  ((word_join:(64)word->(64)word->(128)word)
                                                   ((word_join:(32)word->(32)word->(64)word) (word_subword c (96,32):(32)word) (word_subword c (96,32):(32)word))
                                                   ((word_join:(32)word->(32)word->(64)word) (word_subword c (32,32):(32)word) (word_subword c (32,32):(32)word))))
                                                (192,64):(64)word) (0,32):(32)word)))
                                    (word_mul (word_sx (word_subword (word_subword a (128,64):(64)word) (0,32):(32)word)) 
                                              (word_sx (word_subword (word_subword 
                                                ((word_join:(128)word->(128)word->(256)word)
                                                  ((word_join:(64)word->(64)word->(128)word)
                                                   ((word_join:(32)word->(32)word->(64)word) (word_subword c (224,32):(32)word) (word_subword c (224,32):(32)word))
                                                   ((word_join:(32)word->(32)word->(64)word) (word_subword c (160,32):(32)word) (word_subword c (160,32):(32)word)))
                                                  ((word_join:(64)word->(64)word->(128)word)
                                                   ((word_join:(32)word->(32)word->(64)word) (word_subword c (96,32):(32)word) (word_subword c (96,32):(32)word))
                                                   ((word_join:(32)word->(32)word->(64)word) (word_subword c (32,32):(32)word) (word_subword c (32,32):(32)word))))
                                                (128,64):(64)word) (0,32):(32)word))))
                                   ((word_join:(64)word->(64)word->(128)word)
                                    (word_mul (word_sx (word_subword (word_subword a (64,64):(64)word) (0,32):(32)word)) 
                                              (word_sx (word_subword (word_subword 
                                                ((word_join:(128)word->(128)word->(256)word)
                                                  ((word_join:(64)word->(64)word->(128)word)
                                                   ((word_join:(32)word->(32)word->(64)word) (word_subword c (224,32):(32)word) (word_subword c (224,32):(32)word))
                                                   ((word_join:(32)word->(32)word->(64)word) (word_subword c (160,32):(32)word) (word_subword c (160,32):(32)word)))
                                                  ((word_join:(64)word->(64)word->(128)word)
                                                   ((word_join:(32)word->(32)word->(64)word) (word_subword c (96,32):(32)word) (word_subword c (96,32):(32)word))
                                                   ((word_join:(32)word->(32)word->(64)word) (word_subword c (32,32):(32)word) (word_subword c (32,32):(32)word))))
                                                (64,64):(64)word) (0,32):(32)word)))
                                    (word_mul (word_sx (word_subword (word_subword a (0,64):(64)word) (0,32):(32)word)) 
                                              (word_sx (word_subword (word_subword 
                                                ((word_join:(128)word->(128)word->(256)word)
                                                  ((word_join:(64)word->(64)word->(128)word)
                                                   ((word_join:(32)word->(32)word->(64)word) (word_subword c (224,32):(32)word) (word_subword c (224,32):(32)word))
                                                   ((word_join:(32)word->(32)word->(64)word) (word_subword c (160,32):(32)word) (word_subword c (160,32):(32)word)))
                                                  ((word_join:(64)word->(64)word->(128)word)
                                                   ((word_join:(32)word->(32)word->(64)word) (word_subword c (96,32):(32)word) (word_subword c (96,32):(32)word))
                                                   ((word_join:(32)word->(32)word->(64)word) (word_subword c (32,32):(32)word) (word_subword c (32,32):(32)word))))
                                                (0,64):(64)word) (0,32):(32)word)))))
                                 (128,64):(64)word) (0,32):(32)word))))
                    ((word_join:(64)word->(64)word->(128)word)
                     (word_mul (word_sx (word_subword (word_subword d (64,64):(64)word) (0,32):(32)word)) 
                               (word_sx (word_subword (word_subword 
                                 ((word_join:(128)word->(128)word->(256)word)
                                   ((word_join:(64)word->(64)word->(128)word)
                                    (word_mul (word_sx (word_subword (word_subword a (192,64):(64)word) (0,32):(32)word)) 
                                              (word_sx (word_subword (word_subword 
                                                ((word_join:(128)word->(128)word->(256)word)
                                                  ((word_join:(64)word->(64)word->(128)word)
                                                   ((word_join:(32)word->(32)word->(64)word) (word_subword c (224,32):(32)word) (word_subword c (224,32):(32)word))
                                                   ((word_join:(32)word->(32)word->(64)word) (word_subword c (160,32):(32)word) (word_subword c (160,32):(32)word)))
                                                  ((word_join:(64)word->(64)word->(128)word)
                                                   ((word_join:(32)word->(32)word->(64)word) (word_subword c (96,32):(32)word) (word_subword c (96,32):(32)word))
                                                   ((word_join:(32)word->(32)word->(64)word) (word_subword c (32,32):(32)word) (word_subword c (32,32):(32)word))))
                                                (192,64):(64)word) (0,32):(32)word)))
                                    (word_mul (word_sx (word_subword (word_subword a (128,64):(64)word) (0,32):(32)word)) 
                                              (word_sx (word_subword (word_subword 
                                                ((word_join:(128)word->(128)word->(256)word)
                                                  ((word_join:(64)word->(64)word->(128)word)
                                                   ((word_join:(32)word->(32)word->(64)word) (word_subword c (224,32):(32)word) (word_subword c (224,32):(32)word))
                                                   ((word_join:(32)word->(32)word->(64)word) (word_subword c (160,32):(32)word) (word_subword c (160,32):(32)word)))
                                                  ((word_join:(64)word->(64)word->(128)word)
                                                   ((word_join:(32)word->(32)word->(64)word) (word_subword c (96,32):(32)word) (word_subword c (96,32):(32)word))
                                                   ((word_join:(32)word->(32)word->(64)word) (word_subword c (32,32):(32)word) (word_subword c (32,32):(32)word))))
                                                (128,64):(64)word) (0,32):(32)word))))
                                   ((word_join:(64)word->(64)word->(128)word)
                                    (word_mul (word_sx (word_subword (word_subword a (64,64):(64)word) (0,32):(32)word)) 
                                              (word_sx (word_subword (word_subword 
                                                ((word_join:(128)word->(128)word->(256)word)
                                                  ((word_join:(64)word->(64)word->(128)word)
                                                   ((word_join:(32)word->(32)word->(64)word) (word_subword c (224,32):(32)word) (word_subword c (224,32):(32)word))
                                                   ((word_join:(32)word->(32)word->(64)word) (word_subword c (160,32):(32)word) (word_subword c (160,32):(32)word)))
                                                  ((word_join:(64)word->(64)word->(128)word)
                                                   ((word_join:(32)word->(32)word->(64)word) (word_subword c (96,32):(32)word) (word_subword c (96,32):(32)word))
                                                   ((word_join:(32)word->(32)word->(64)word) (word_subword c (32,32):(32)word) (word_subword c (32,32):(32)word))))
                                                (64,64):(64)word) (0,32):(32)word)))
                                    (word_mul (word_sx (word_subword (word_subword a (0,64):(64)word) (0,32):(32)word)) 
                                              (word_sx (word_subword (word_subword 
                                                ((word_join:(128)word->(128)word->(256)word)
                                                  ((word_join:(64)word->(64)word->(128)word)
                                                   ((word_join:(32)word->(32)word->(64)word) (word_subword c (224,32):(32)word) (word_subword c (224,32):(32)word))
                                                   ((word_join:(32)word->(32)word->(64)word) (word_subword c (160,32):(32)word) (word_subword c (160,32):(32)word)))
                                                  ((word_join:(64)word->(64)word->(128)word)
                                                   ((word_join:(32)word->(32)word->(64)word) (word_subword c (96,32):(32)word) (word_subword c (96,32):(32)word))
                                                   ((word_join:(32)word->(32)word->(64)word) (word_subword c (32,32):(32)word) (word_subword c (32,32):(32)word))))
                                                (0,64):(64)word) (0,32):(32)word)))))
                                 (64,64):(64)word) (0,32):(32)word)))
                     (word_mul (word_sx (word_subword (word_subword d (0,64):(64)word) (0,32):(32)word)) 
                               (word_sx (word_subword (word_subword 
                                 ((word_join:(128)word->(128)word->(256)word)
                                   ((word_join:(64)word->(64)word->(128)word)
                                    (word_mul (word_sx (word_subword (word_subword a (192,64):(64)word) (0,32):(32)word)) 
                                              (word_sx (word_subword (word_subword 
                                                ((word_join:(128)word->(128)word->(256)word)
                                                  ((word_join:(64)word->(64)word->(128)word)
                                                   ((word_join:(32)word->(32)word->(64)word) (word_subword c (224,32):(32)word) (word_subword c (224,32):(32)word))
                                                   ((word_join:(32)word->(32)word->(64)word) (word_subword c (160,32):(32)word) (word_subword c (160,32):(32)word)))
                                                  ((word_join:(64)word->(64)word->(128)word)
                                                   ((word_join:(32)word->(32)word->(64)word) (word_subword c (96,32):(32)word) (word_subword c (96,32):(32)word))
                                                   ((word_join:(32)word->(32)word->(64)word) (word_subword c (32,32):(32)word) (word_subword c (32,32):(32)word))))
                                                (192,64):(64)word) (0,32):(32)word)))
                                    (word_mul (word_sx (word_subword (word_subword a (128,64):(64)word) (0,32):(32)word)) 
                                              (word_sx (word_subword (word_subword 
                                                ((word_join:(128)word->(128)word->(256)word)
                                                  ((word_join:(64)word->(64)word->(128)word)
                                                   ((word_join:(32)word->(32)word->(64)word) (word_subword c (224,32):(32)word) (word_subword c (224,32):(32)word))
                                                   ((word_join:(32)word->(32)word->(64)word) (word_subword c (160,32):(32)word) (word_subword c (160,32):(32)word)))
                                                  ((word_join:(64)word->(64)word->(128)word)
                                                   ((word_join:(32)word->(32)word->(64)word) (word_subword c (96,32):(32)word) (word_subword c (96,32):(32)word))
                                                   ((word_join:(32)word->(32)word->(64)word) (word_subword c (32,32):(32)word) (word_subword c (32,32):(32)word))))
                                                (128,64):(64)word) (0,32):(32)word))))
                                   ((word_join:(64)word->(64)word->(128)word)
                                    (word_mul (word_sx (word_subword (word_subword a (64,64):(64)word) (0,32):(32)word)) 
                                              (word_sx (word_subword (word_subword 
                                                ((word_join:(128)word->(128)word->(256)word)
                                                  ((word_join:(64)word->(64)word->(128)word)
                                                   ((word_join:(32)word->(32)word->(64)word) (word_subword c (224,32):(32)word) (word_subword c (224,32):(32)word))
                                                   ((word_join:(32)word->(32)word->(64)word) (word_subword c (160,32):(32)word) (word_subword c (160,32):(32)word)))
                                                  ((word_join:(64)word->(64)word->(128)word)
                                                   ((word_join:(32)word->(32)word->(64)word) (word_subword c (96,32):(32)word) (word_subword c (96,32):(32)word))
                                                   ((word_join:(32)word->(32)word->(64)word) (word_subword c (32,32):(32)word) (word_subword c (32,32):(32)word))))
                                                (64,64):(64)word) (0,32):(32)word)))
                                    (word_mul (word_sx (word_subword (word_subword a (0,64):(64)word) (0,32):(32)word)) 
                                              (word_sx (word_subword (word_subword 
                                                ((word_join:(128)word->(128)word->(256)word)
                                                  ((word_join:(64)word->(64)word->(128)word)
                                                   ((word_join:(32)word->(32)word->(64)word) (word_subword c (224,32):(32)word) (word_subword c (224,32):(32)word))
                                                   ((word_join:(32)word->(32)word->(64)word) (word_subword c (160,32):(32)word) (word_subword c (160,32):(32)word)))
                                                  ((word_join:(64)word->(64)word->(128)word)
                                                   ((word_join:(32)word->(32)word->(64)word) (word_subword c (96,32):(32)word) (word_subword c (96,32):(32)word))
                                                   ((word_join:(32)word->(32)word->(64)word) (word_subword c (32,32):(32)word) (word_subword c (32,32):(32)word))))
                                                (0,64):(64)word) (0,32):(32)word)))))
                                 (0,64):(64)word) (0,32):(32)word)))) /\
                  read YMM8 s = 
                  (word_join:(128)word->(128)word->(256)word)
                    ((word_join:(64)word->(64)word->(128)word)
                     ((word_join:(32)word->(32)word->(64)word) 
                      (word_subword 
                        ((word_join:(128)word->(128)word->(256)word)
                          ((word_join:(64)word->(64)word->(128)word)
                           (word_mul (word_sx (word_subword (word_subword b (192,64):(64)word) (0,32):(32)word)) 
                                     (word_sx (word_subword (word_subword c (192,64):(64)word) (0,32):(32)word)))
                           (word_mul (word_sx (word_subword (word_subword b (128,64):(64)word) (0,32):(32)word)) 
                                     (word_sx (word_subword (word_subword c (128,64):(64)word) (0,32):(32)word))))
                          ((word_join:(64)word->(64)word->(128)word)
                           (word_mul (word_sx (word_subword (word_subword b (64,64):(64)word) (0,32):(32)word)) 
                                     (word_sx (word_subword (word_subword c (64,64):(64)word) (0,32):(32)word)))
                           (word_mul (word_sx (word_subword (word_subword b (0,64):(64)word) (0,32):(32)word)) 
                                     (word_sx (word_subword (word_subword c (0,64):(64)word) (0,32):(32)word)))))
                        (224,32):(32)word) 
                      (word_subword 
                        ((word_join:(128)word->(128)word->(256)word)
                          ((word_join:(64)word->(64)word->(128)word)
                           (word_mul (word_sx (word_subword (word_subword b (192,64):(64)word) (0,32):(32)word)) 
                                     (word_sx (word_subword (word_subword c (192,64):(64)word) (0,32):(32)word)))
                           (word_mul (word_sx (word_subword (word_subword b (128,64):(64)word) (0,32):(32)word)) 
                                     (word_sx (word_subword (word_subword c (128,64):(64)word) (0,32):(32)word))))
                          ((word_join:(64)word->(64)word->(128)word)
                           (word_mul (word_sx (word_subword (word_subword b (64,64):(64)word) (0,32):(32)word)) 
                                     (word_sx (word_subword (word_subword c (64,64):(64)word) (0,32):(32)word)))
                           (word_mul (word_sx (word_subword (word_subword b (0,64):(64)word) (0,32):(32)word)) 
                                     (word_sx (word_subword (word_subword c (0,64):(64)word) (0,32):(32)word)))))
                        (224,32):(32)word))
                     ((word_join:(32)word->(32)word->(64)word) 
                      (word_subword 
                        ((word_join:(128)word->(128)word->(256)word)
                          ((word_join:(64)word->(64)word->(128)word)
                           (word_mul (word_sx (word_subword (word_subword b (192,64):(64)word) (0,32):(32)word)) 
                                     (word_sx (word_subword (word_subword c (192,64):(64)word) (0,32):(32)word)))
                           (word_mul (word_sx (word_subword (word_subword b (128,64):(64)word) (0,32):(32)word)) 
                                     (word_sx (word_subword (word_subword c (128,64):(64)word) (0,32):(32)word))))
                          ((word_join:(64)word->(64)word->(128)word)
                           (word_mul (word_sx (word_subword (word_subword b (64,64):(64)word) (0,32):(32)word)) 
                                     (word_sx (word_subword (word_subword c (64,64):(64)word) (0,32):(32)word)))
                           (word_mul (word_sx (word_subword (word_subword b (0,64):(64)word) (0,32):(32)word)) 
                                     (word_sx (word_subword (word_subword c (0,64):(64)word) (0,32):(32)word)))))
                        (160,32):(32)word) 
                      (word_subword 
                        ((word_join:(128)word->(128)word->(256)word)
                          ((word_join:(64)word->(64)word->(128)word)
                           (word_mul (word_sx (word_subword (word_subword b (192,64):(64)word) (0,32):(32)word)) 
                                     (word_sx (word_subword (word_subword c (192,64):(64)word) (0,32):(32)word)))
                           (word_mul (word_sx (word_subword (word_subword b (128,64):(64)word) (0,32):(32)word)) 
                                     (word_sx (word_subword (word_subword c (128,64):(64)word) (0,32):(32)word))))
                          ((word_join:(64)word->(64)word->(128)word)
                           (word_mul (word_sx (word_subword (word_subword b (64,64):(64)word) (0,32):(32)word)) 
                                     (word_sx (word_subword (word_subword c (64,64):(64)word) (0,32):(32)word)))
                           (word_mul (word_sx (word_subword (word_subword b (0,64):(64)word) (0,32):(32)word)) 
                                     (word_sx (word_subword (word_subword c (0,64):(64)word) (0,32):(32)word)))))
                        (160,32):(32)word)))
                    ((word_join:(64)word->(64)word->(128)word)
                     ((word_join:(32)word->(32)word->(64)word) 
                      (word_subword 
                        ((word_join:(128)word->(128)word->(256)word)
                          ((word_join:(64)word->(64)word->(128)word)
                           (word_mul (word_sx (word_subword (word_subword b (192,64):(64)word) (0,32):(32)word)) 
                                     (word_sx (word_subword (word_subword c (192,64):(64)word) (0,32):(32)word)))
                           (word_mul (word_sx (word_subword (word_subword b (128,64):(64)word) (0,32):(32)word)) 
                                     (word_sx (word_subword (word_subword c (128,64):(64)word) (0,32):(32)word))))
                          ((word_join:(64)word->(64)word->(128)word)
                           (word_mul (word_sx (word_subword (word_subword b (64,64):(64)word) (0,32):(32)word)) 
                                     (word_sx (word_subword (word_subword c (64,64):(64)word) (0,32):(32)word)))
                           (word_mul (word_sx (word_subword (word_subword b (0,64):(64)word) (0,32):(32)word)) 
                                     (word_sx (word_subword (word_subword c (0,64):(64)word) (0,32):(32)word)))))
                        (96,32):(32)word) 
                      (word_subword 
                        ((word_join:(128)word->(128)word->(256)word)
                          ((word_join:(64)word->(64)word->(128)word)
                           (word_mul (word_sx (word_subword (word_subword b (192,64):(64)word) (0,32):(32)word)) 
                                     (word_sx (word_subword (word_subword c (192,64):(64)word) (0,32):(32)word)))
                           (word_mul (word_sx (word_subword (word_subword b (128,64):(64)word) (0,32):(32)word)) 
                                     (word_sx (word_subword (word_subword c (128,64):(64)word) (0,32):(32)word))))
                          ((word_join:(64)word->(64)word->(128)word)
                           (word_mul (word_sx (word_subword (word_subword b (64,64):(64)word) (0,32):(32)word)) 
                                     (word_sx (word_subword (word_subword c (64,64):(64)word) (0,32):(32)word)))
                           (word_mul (word_sx (word_subword (word_subword b (0,64):(64)word) (0,32):(32)word)) 
                                     (word_sx (word_subword (word_subword c (0,64):(64)word) (0,32):(32)word)))))
                        (96,32):(32)word))
                     ((word_join:(32)word->(32)word->(64)word) 
                      (word_subword 
                        ((word_join:(128)word->(128)word->(256)word)
                          ((word_join:(64)word->(64)word->(128)word)
                           (word_mul (word_sx (word_subword (word_subword b (192,64):(64)word) (0,32):(32)word)) 
                                     (word_sx (word_subword (word_subword c (192,64):(64)word) (0,32):(32)word)))
                           (word_mul (word_sx (word_subword (word_subword b (128,64):(64)word) (0,32):(32)word)) 
                                     (word_sx (word_subword (word_subword c (128,64):(64)word) (0,32):(32)word))))
                          ((word_join:(64)word->(64)word->(128)word)
                           (word_mul (word_sx (word_subword (word_subword b (64,64):(64)word) (0,32):(32)word)) 
                                     (word_sx (word_subword (word_subword c (64,64):(64)word) (0,32):(32)word)))
                           (word_mul (word_sx (word_subword (word_subword b (0,64):(64)word) (0,32):(32)word)) 
                                     (word_sx (word_subword (word_subword c (0,64):(64)word) (0,32):(32)word)))))
                        (32,32):(32)word) 
                      (word_subword 
                        ((word_join:(128)word->(128)word->(256)word)
                          ((word_join:(64)word->(64)word->(128)word)
                           (word_mul (word_sx (word_subword (word_subword b (192,64):(64)word) (0,32):(32)word)) 
                                     (word_sx (word_subword (word_subword c (192,64):(64)word) (0,32):(32)word)))
                           (word_mul (word_sx (word_subword (word_subword b (128,64):(64)word) (0,32):(32)word)) 
                                     (word_sx (word_subword (word_subword c (128,64):(64)word) (0,32):(32)word))))
                          ((word_join:(64)word->(64)word->(128)word)
                           (word_mul (word_sx (word_subword (word_subword b (64,64):(64)word) (0,32):(32)word)) 
                                     (word_sx (word_subword (word_subword c (64,64):(64)word) (0,32):(32)word)))
                           (word_mul (word_sx (word_subword (word_subword b (0,64):(64)word) (0,32):(32)word)) 
                                     (word_sx (word_subword (word_subword c (0,64):(64)word) (0,32):(32)word)))))
                        (32,32):(32)word))) /\
                  read YMM12 s = 
                  (word_join:(128)word->(128)word->(256)word)
                    ((word_join:(64)word->(64)word->(128)word)
                     (word_mul (word_sx (word_subword (word_subword b (192,64):(64)word) (0,32):(32)word)) 
                               (word_sx (word_subword (word_subword 
                                 ((word_join:(128)word->(128)word->(256)word)
                                   ((word_join:(64)word->(64)word->(128)word)
                                    ((word_join:(32)word->(32)word->(64)word) (word_subword c (224,32):(32)word) (word_subword c (224,32):(32)word))
                                    ((word_join:(32)word->(32)word->(64)word) (word_subword c (160,32):(32)word) (word_subword c (160,32):(32)word)))
                                   ((word_join:(64)word->(64)word->(128)word)
                                    ((word_join:(32)word->(32)word->(64)word) (word_subword c (96,32):(32)word) (word_subword c (96,32):(32)word))
                                    ((word_join:(32)word->(32)word->(64)word) (word_subword c (32,32):(32)word) (word_subword c (32,32):(32)word))))
                                 (192,64):(64)word) (0,32):(32)word)))
                     (word_mul (word_sx (word_subword (word_subword b (128,64):(64)word) (0,32):(32)word)) 
                               (word_sx (word_subword (word_subword 
                                 ((word_join:(128)word->(128)word->(256)word)
                                   ((word_join:(64)word->(64)word->(128)word)
                                    ((word_join:(32)word->(32)word->(64)word) (word_subword c (224,32):(32)word) (word_subword c (224,32):(32)word))
                                    ((word_join:(32)word->(32)word->(64)word) (word_subword c (160,32):(32)word) (word_subword c (160,32):(32)word)))
                                   ((word_join:(64)word->(64)word->(128)word)
                                    ((word_join:(32)word->(32)word->(64)word) (word_subword c (96,32):(32)word) (word_subword c (96,32):(32)word))
                                    ((word_join:(32)word->(32)word->(64)word) (word_subword c (32,32):(32)word) (word_subword c (32,32):(32)word))))
                                 (128,64):(64)word) (0,32):(32)word))))
                    ((word_join:(64)word->(64)word->(128)word)
                     (word_mul (word_sx (word_subword (word_subword b (64,64):(64)word) (0,32):(32)word)) 
                               (word_sx (word_subword (word_subword 
                                 ((word_join:(128)word->(128)word->(256)word)
                                   ((word_join:(64)word->(64)word->(128)word)
                                    ((word_join:(32)word->(32)word->(64)word) (word_subword c (224,32):(32)word) (word_subword c (224,32):(32)word))
                                    ((word_join:(32)word->(32)word->(64)word) (word_subword c (160,32):(32)word) (word_subword c (160,32):(32)word)))
                                   ((word_join:(64)word->(64)word->(128)word)
                                    ((word_join:(32)word->(32)word->(64)word) (word_subword c (96,32):(32)word) (word_subword c (96,32):(32)word))
                                    ((word_join:(32)word->(32)word->(64)word) (word_subword c (32,32):(32)word) (word_subword c (32,32):(32)word))))
                                 (64,64):(64)word) (0,32):(32)word)))
                     (word_mul (word_sx (word_subword (word_subword b (0,64):(64)word) (0,32):(32)word)) 
                               (word_sx (word_subword (word_subword 
                                 ((word_join:(128)word->(128)word->(256)word)
                                   ((word_join:(64)word->(64)word->(128)word)
                                    ((word_join:(32)word->(32)word->(64)word) (word_subword c (224,32):(32)word) (word_subword c (224,32):(32)word))
                                    ((word_join:(32)word->(32)word->(64)word) (word_subword c (160,32):(32)word) (word_subword c (160,32):(32)word)))
                                   ((word_join:(64)word->(64)word->(128)word)
                                    ((word_join:(32)word->(32)word->(64)word) (word_subword c (96,32):(32)word) (word_subword c (96,32):(32)word))
                                    ((word_join:(32)word->(32)word->(64)word) (word_subword c (32,32):(32)word) (word_subword c (32,32):(32)word))))
                                 (0,64):(64)word) (0,32):(32)word)))))
             (MAYCHANGE [RIP] ,, MAYCHANGE [ZMM13; ZMM12; ZMM14; ZMM8] ,, MAYCHANGE SOME_FLAGS)`,
  REWRITE_TAC [SOME_FLAGS; fst MLDSA_MONT_8INSTR_EXEC] THEN
  REPEAT STRIP_TAC THEN
  ENSURES_INIT_TAC "s0" THEN
  X86_STEPS_TAC MLDSA_MONT_8INSTR_EXEC (1--8) THEN
  ENSURES_FINAL_STATE_TAC THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[MAYCHANGE] THEN
  ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN
  TRY (REFL_TAC) THEN
  ALL_TAC);;

(* ------------------------------------------------------------------------- *)
(* Instruction sequence analysis:                                            *)
(* 1. vpmuldq ymm13, ymm1, ymm8    # YMM13 = YMM1 * YMM8 (even elements)     *)
(* 2. vmovshdup ymm12, ymm8         # YMM12 = shuffle-duplicate YMM8         *)
(* 3. vpmuldq ymm14, ymm1, ymm12    # YMM14 = YMM1 * YMM12 (shuffled)        *)
(* 4. vpmuldq ymm8, ymm2, ymm8      # YMM8 = YMM2 * YMM8 (overwrite)         *)
(* 5. vpmuldq ymm12, ymm2, ymm12    # YMM12 = YMM2 * YMM12 (overwrite)       *)
(* 6. vpmuldq ymm13, ymm0, ymm13    # YMM13 = YMM0 * YMM13 (overwrite)       *)
(* 7. vpmuldq ymm14, ymm0, ymm14    # YMM14 = YMM0 * YMM14 (overwrite)       *)
(* 8. vmovshdup ymm8, ymm8          # YMM8 = shuffle-duplicate YMM8          *)
(*                                                                           *)
(* This extends the 7-instruction sequence with a final shuffle operation    *)
(* on YMM8, creating a shuffle-duplicate pattern of the computed result.     *)
(* Final results: YMM13 = YMM0 * (YMM1 * YMM8)                               *)
(*                YMM14 = YMM0 * (YMM1 * shuffled YMM8)                      *)
(*                YMM8 = shuffle-duplicate of (YMM2 * YMM8)                  *)
(*                YMM12 = YMM2 * shuffled YMM8                               *)
(* ------------------------------------------------------------------------- *)
