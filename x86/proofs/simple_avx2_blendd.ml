(* ========================================================================= *)
(* Simple AVX2 vector blend proof for ML-DSA development                    *)
(* ========================================================================= *)

needs "x86/proofs/base.ml";;

(**** print_literal_from_elf "x86/mldsa/simple_avx2_vpblendd.o";;
 ****)

let simple_avx2_blendd_mc = define_assert_from_elf "simple_avx2_blendd_mc" "x86/mldsa/simple_avx2_vpblendd.o"
[
  0xc4; 0x43; 0x3d; 0x02; 0xc4; 0xaa
                           (* VPBLENDD (%_% ymm8) (%_% ymm8) (%_% ymm12) (Imm8 (word 170)) *)
];;

let SIMPLE_AVX2_BLENDD_EXEC = X86_MK_EXEC_RULE simple_avx2_blendd_mc;;

(* ------------------------------------------------------------------------- *)
(* Proof.                                                                    *)
(* ------------------------------------------------------------------------- *)

let SIMPLE_AVX2_BLENDD_CORRECT = prove
 (`forall pc a b.
        ensures x86
             (\s. bytes_loaded s (word pc) simple_avx2_blendd_mc /\
                  read RIP s = word pc /\
                  read YMM8 s = a /\
                  read YMM12 s = b)
             (\s. read RIP s = word (pc + LENGTH simple_avx2_blendd_mc) /\
                  read YMM8 s = (msimd8:((1)word->(32)word->(32)word->(32)word)->(8)word->(256)word->(256)word->(256)word) 
                                (\(i:(1)word) (x:(32)word) (y:(32)word). if i = word 1 then x else y) 
                                (word 170:(8)word) 
                                (a:(256)word) 
                                (b:(256)word))
             (MAYCHANGE [RIP] ,, MAYCHANGE [YMM8])`,
  REWRITE_TAC [fst SIMPLE_AVX2_BLENDD_EXEC] THEN
  REPEAT STRIP_TAC THEN
  ENSURES_INIT_TAC "s0" THEN
  X86_STEPS_TAC SIMPLE_AVX2_BLENDD_EXEC (1--1) THEN
  ENSURES_FINAL_STATE_TAC THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[MAYCHANGE] THEN
  ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN
  TRY (REFL_TAC) THEN
  ALL_TAC);;


  (* Note: The symbolic execution produces the msimd8 specification:
   read YMM8 s1 = msimd8 (\i x y. if i = word 1 then x else y) (word 170) a b
   
   This represents the VPBLENDD operation where:
   - Mask 170 = 0xAA = 10101010 binary  
   - For each bit i: if bit=1 use YMM12 (x), if bit=0 use YMM8 (y)
   - Result: blend elements from YMM8 and YMM12 based on immediate mask

*)
