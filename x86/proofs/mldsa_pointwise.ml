(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Pointwise multiplication of polynomials in NTT domain for ML-DSA.         *)
(* ========================================================================= *)

needs "x86/proofs/base.ml";;
needs "common/mlkem_mldsa.ml";;

(*** print_literal_from_elf "x86/mldsa/mldsa_pointwise.o";;
 ***)
let mldsa_pointwise_mc = define_assert_from_elf "mldsa_pointwise_mc" "x86/mldsa/mldsa_pointwise.o"
[
  0xf3; 0x0f; 0x1e; 0xfa;  (* ENDBR64 *)
  0xc5; 0xfd; 0x6f; 0x01;  (* VMOVDQA (%_% ymm0) (Memop Word256 (%% (rcx,0))) *)
  0xc5; 0xfd; 0x6f; 0x49; 0x20;
                           (* VMOVDQA (%_% ymm1) (Memop Word256 (%% (rcx,32))) *)
  0x31; 0xc0;              (* XOR (% eax) (% eax) *)
  0xc5; 0xfd; 0x6f; 0x16;  (* VMOVDQA (%_% ymm2) (Memop Word256 (%% (rsi,0))) *)
  0xc5; 0xfd; 0x6f; 0x66; 0x20;
                           (* VMOVDQA (%_% ymm4) (Memop Word256 (%% (rsi,32))) *)
  0xc5; 0xfd; 0x6f; 0x76; 0x40;
                           (* VMOVDQA (%_% ymm6) (Memop Word256 (%% (rsi,64))) *)
  0xc5; 0x7d; 0x6f; 0x12;  (* VMOVDQA (%_% ymm10) (Memop Word256 (%% (rdx,0))) *)
  0xc5; 0x7d; 0x6f; 0x62; 0x20;
                           (* VMOVDQA (%_% ymm12) (Memop Word256 (%% (rdx,32))) *)
  0xc5; 0x7d; 0x6f; 0x72; 0x40;
                           (* VMOVDQA (%_% ymm14) (Memop Word256 (%% (rdx,64))) *)
  0xc5; 0xe5; 0x73; 0xd2; 0x20;
                           (* VPSRLQ (%_% ymm3) (%_% ymm2) (Imm8 (word 32)) *)
  0xc5; 0xd5; 0x73; 0xd4; 0x20;
                           (* VPSRLQ (%_% ymm5) (%_% ymm4) (Imm8 (word 32)) *)
  0xc5; 0xfe; 0x16; 0xfe;  (* VMOVSHDUP (%_% ymm7) (%_% ymm6) *)
  0xc4; 0xc1; 0x25; 0x73; 0xd2; 0x20;
                           (* VPSRLQ (%_% ymm11) (%_% ymm10) (Imm8 (word 32)) *)
  0xc4; 0xc1; 0x15; 0x73; 0xd4; 0x20;
                           (* VPSRLQ (%_% ymm13) (%_% ymm12) (Imm8 (word 32)) *)
  0xc4; 0x41; 0x7e; 0x16; 0xfe;
                           (* VMOVSHDUP (%_% ymm15) (%_% ymm14) *)
  0xc4; 0xc2; 0x6d; 0x28; 0xd2;
                           (* VPMULDQ (%_% ymm2) (%_% ymm2) (%_% ymm10) *)
  0xc4; 0xc2; 0x65; 0x28; 0xdb;
                           (* VPMULDQ (%_% ymm3) (%_% ymm3) (%_% ymm11) *)
  0xc4; 0xc2; 0x5d; 0x28; 0xe4;
                           (* VPMULDQ (%_% ymm4) (%_% ymm4) (%_% ymm12) *)
  0xc4; 0xc2; 0x55; 0x28; 0xed;
                           (* VPMULDQ (%_% ymm5) (%_% ymm5) (%_% ymm13) *)
  0xc4; 0xc2; 0x4d; 0x28; 0xf6;
                           (* VPMULDQ (%_% ymm6) (%_% ymm6) (%_% ymm14) *)
  0xc4; 0xc2; 0x45; 0x28; 0xff;
                           (* VPMULDQ (%_% ymm7) (%_% ymm7) (%_% ymm15) *)
  0xc4; 0x62; 0x7d; 0x28; 0xd2;
                           (* VPMULDQ (%_% ymm10) (%_% ymm0) (%_% ymm2) *)
  0xc4; 0x62; 0x7d; 0x28; 0xdb;
                           (* VPMULDQ (%_% ymm11) (%_% ymm0) (%_% ymm3) *)
  0xc4; 0x62; 0x7d; 0x28; 0xe4;
                           (* VPMULDQ (%_% ymm12) (%_% ymm0) (%_% ymm4) *)
  0xc4; 0x62; 0x7d; 0x28; 0xed;
                           (* VPMULDQ (%_% ymm13) (%_% ymm0) (%_% ymm5) *)
  0xc4; 0x62; 0x7d; 0x28; 0xf6;
                           (* VPMULDQ (%_% ymm14) (%_% ymm0) (%_% ymm6) *)
  0xc4; 0x62; 0x7d; 0x28; 0xff;
                           (* VPMULDQ (%_% ymm15) (%_% ymm0) (%_% ymm7) *)
  0xc4; 0x42; 0x75; 0x28; 0xd2;
                           (* VPMULDQ (%_% ymm10) (%_% ymm1) (%_% ymm10) *)
  0xc4; 0x42; 0x75; 0x28; 0xdb;
                           (* VPMULDQ (%_% ymm11) (%_% ymm1) (%_% ymm11) *)
  0xc4; 0x42; 0x75; 0x28; 0xe4;
                           (* VPMULDQ (%_% ymm12) (%_% ymm1) (%_% ymm12) *)
  0xc4; 0x42; 0x75; 0x28; 0xed;
                           (* VPMULDQ (%_% ymm13) (%_% ymm1) (%_% ymm13) *)
  0xc4; 0x42; 0x75; 0x28; 0xf6;
                           (* VPMULDQ (%_% ymm14) (%_% ymm1) (%_% ymm14) *)
  0xc4; 0x42; 0x75; 0x28; 0xff;
                           (* VPMULDQ (%_% ymm15) (%_% ymm1) (%_% ymm15) *)
  0xc4; 0xc1; 0x6d; 0xfb; 0xd2;
                           (* VPSUBQ (%_% ymm2) (%_% ymm2) (%_% ymm10) *)
  0xc4; 0xc1; 0x65; 0xfb; 0xdb;
                           (* VPSUBQ (%_% ymm3) (%_% ymm3) (%_% ymm11) *)
  0xc4; 0xc1; 0x5d; 0xfb; 0xe4;
                           (* VPSUBQ (%_% ymm4) (%_% ymm4) (%_% ymm12) *)
  0xc4; 0xc1; 0x55; 0xfb; 0xed;
                           (* VPSUBQ (%_% ymm5) (%_% ymm5) (%_% ymm13) *)
  0xc4; 0xc1; 0x4d; 0xfb; 0xf6;
                           (* VPSUBQ (%_% ymm6) (%_% ymm6) (%_% ymm14) *)
  0xc4; 0xc1; 0x45; 0xfb; 0xff;
                           (* VPSUBQ (%_% ymm7) (%_% ymm7) (%_% ymm15) *)
  0xc5; 0xed; 0x73; 0xd2; 0x20;
                           (* VPSRLQ (%_% ymm2) (%_% ymm2) (Imm8 (word 32)) *)
  0xc5; 0xdd; 0x73; 0xd4; 0x20;
                           (* VPSRLQ (%_% ymm4) (%_% ymm4) (Imm8 (word 32)) *)
  0xc5; 0xfe; 0x16; 0xf6;  (* VMOVSHDUP (%_% ymm6) (%_% ymm6) *)
  0xc4; 0xe3; 0x6d; 0x02; 0xd3; 0xaa;
                           (* VPBLENDD (%_% ymm2) (%_% ymm2) (%_% ymm3) (Imm8 (word 170)) *)
  0xc4; 0xe3; 0x5d; 0x02; 0xe5; 0xaa;
                           (* VPBLENDD (%_% ymm4) (%_% ymm4) (%_% ymm5) (Imm8 (word 170)) *)
  0xc4; 0xe3; 0x4d; 0x02; 0xf7; 0xaa;
                           (* VPBLENDD (%_% ymm6) (%_% ymm6) (%_% ymm7) (Imm8 (word 170)) *)
  0xc5; 0xfd; 0x7f; 0x17;  (* VMOVDQA (Memop Word256 (%% (rdi,0))) (%_% ymm2) *)
  0xc5; 0xfd; 0x7f; 0x67; 0x20;
                           (* VMOVDQA (Memop Word256 (%% (rdi,32))) (%_% ymm4) *)
  0xc5; 0xfd; 0x7f; 0x77; 0x40;
                           (* VMOVDQA (Memop Word256 (%% (rdi,64))) (%_% ymm6) *)
  0x48; 0x83; 0xc7; 0x60;  (* ADD (% rdi) (Imm8 (word 96)) *)
  0x48; 0x83; 0xc6; 0x60;  (* ADD (% rsi) (Imm8 (word 96)) *)
  0x48; 0x83; 0xc2; 0x60;  (* ADD (% rdx) (Imm8 (word 96)) *)
  0x83; 0xc0; 0x01;        (* ADD (% eax) (Imm8 (word 1)) *)
  0x83; 0xf8; 0x0a;        (* CMP (% eax) (Imm8 (word 10)) *)
  0x0f; 0x82; 0x07; 0xff; 0xff; 0xff;
                           (* JB (Imm32 (word 4294967047)) *)
  0xc5; 0xfd; 0x6f; 0x16;  (* VMOVDQA (%_% ymm2) (Memop Word256 (%% (rsi,0))) *)
  0xc5; 0xfd; 0x6f; 0x66; 0x20;
                           (* VMOVDQA (%_% ymm4) (Memop Word256 (%% (rsi,32))) *)
  0xc5; 0x7d; 0x6f; 0x12;  (* VMOVDQA (%_% ymm10) (Memop Word256 (%% (rdx,0))) *)
  0xc5; 0x7d; 0x6f; 0x62; 0x20;
                           (* VMOVDQA (%_% ymm12) (Memop Word256 (%% (rdx,32))) *)
  0xc5; 0xe5; 0x73; 0xd2; 0x20;
                           (* VPSRLQ (%_% ymm3) (%_% ymm2) (Imm8 (word 32)) *)
  0xc5; 0xd5; 0x73; 0xd4; 0x20;
                           (* VPSRLQ (%_% ymm5) (%_% ymm4) (Imm8 (word 32)) *)
  0xc4; 0x41; 0x7e; 0x16; 0xda;
                           (* VMOVSHDUP (%_% ymm11) (%_% ymm10) *)
  0xc4; 0x41; 0x7e; 0x16; 0xec;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm12) *)
  0xc4; 0xc2; 0x6d; 0x28; 0xd2;
                           (* VPMULDQ (%_% ymm2) (%_% ymm2) (%_% ymm10) *)
  0xc4; 0xc2; 0x65; 0x28; 0xdb;
                           (* VPMULDQ (%_% ymm3) (%_% ymm3) (%_% ymm11) *)
  0xc4; 0xc2; 0x5d; 0x28; 0xe4;
                           (* VPMULDQ (%_% ymm4) (%_% ymm4) (%_% ymm12) *)
  0xc4; 0xc2; 0x55; 0x28; 0xed;
                           (* VPMULDQ (%_% ymm5) (%_% ymm5) (%_% ymm13) *)
  0xc4; 0x62; 0x7d; 0x28; 0xd2;
                           (* VPMULDQ (%_% ymm10) (%_% ymm0) (%_% ymm2) *)
  0xc4; 0x62; 0x7d; 0x28; 0xdb;
                           (* VPMULDQ (%_% ymm11) (%_% ymm0) (%_% ymm3) *)
  0xc4; 0x62; 0x7d; 0x28; 0xe4;
                           (* VPMULDQ (%_% ymm12) (%_% ymm0) (%_% ymm4) *)
  0xc4; 0x62; 0x7d; 0x28; 0xed;
                           (* VPMULDQ (%_% ymm13) (%_% ymm0) (%_% ymm5) *)
  0xc4; 0x42; 0x75; 0x28; 0xd2;
                           (* VPMULDQ (%_% ymm10) (%_% ymm1) (%_% ymm10) *)
  0xc4; 0x42; 0x75; 0x28; 0xdb;
                           (* VPMULDQ (%_% ymm11) (%_% ymm1) (%_% ymm11) *)
  0xc4; 0x42; 0x75; 0x28; 0xe4;
                           (* VPMULDQ (%_% ymm12) (%_% ymm1) (%_% ymm12) *)
  0xc4; 0x42; 0x75; 0x28; 0xed;
                           (* VPMULDQ (%_% ymm13) (%_% ymm1) (%_% ymm13) *)
  0xc4; 0xc1; 0x6d; 0xfb; 0xd2;
                           (* VPSUBQ (%_% ymm2) (%_% ymm2) (%_% ymm10) *)
  0xc4; 0xc1; 0x65; 0xfb; 0xdb;
                           (* VPSUBQ (%_% ymm3) (%_% ymm3) (%_% ymm11) *)
  0xc4; 0xc1; 0x5d; 0xfb; 0xe4;
                           (* VPSUBQ (%_% ymm4) (%_% ymm4) (%_% ymm12) *)
  0xc4; 0xc1; 0x55; 0xfb; 0xed;
                           (* VPSUBQ (%_% ymm5) (%_% ymm5) (%_% ymm13) *)
  0xc5; 0xed; 0x73; 0xd2; 0x20;
                           (* VPSRLQ (%_% ymm2) (%_% ymm2) (Imm8 (word 32)) *)
  0xc5; 0xfe; 0x16; 0xe4;  (* VMOVSHDUP (%_% ymm4) (%_% ymm4) *)
  0xc4; 0xe3; 0x65; 0x02; 0xd2; 0x55;
                           (* VPBLENDD (%_% ymm2) (%_% ymm3) (%_% ymm2) (Imm8 (word 85)) *)
  0xc4; 0xe3; 0x55; 0x02; 0xe4; 0x55;
                           (* VPBLENDD (%_% ymm4) (%_% ymm5) (%_% ymm4) (Imm8 (word 85)) *)
  0xc5; 0xfd; 0x7f; 0x17;  (* VMOVDQA (Memop Word256 (%% (rdi,0))) (%_% ymm2) *)
  0xc5; 0xfd; 0x7f; 0x67; 0x20;
                           (* VMOVDQA (Memop Word256 (%% (rdi,32))) (%_% ymm4) *)
  0xc3                     (* RET *)
];;

let mldsa_pointwise_tmc = define_trimmed "mldsa_pointwise_tmc" mldsa_pointwise_mc;;
let MLDSA_POINTWISE_TMC_EXEC = X86_MK_CORE_EXEC_RULE mldsa_pointwise_tmc;;

(* ------------------------------------------------------------------------- *)
(* mldsa_pointwise uses mldsa_pointwise_mont from common/mlkem_mldsa.ml      *)
(* Defined as: mldsa_montred(iword(ival a * ival b))                         *)
(* CONGBOUND_MLDSA_POINTWISE_MONT in mlkem_mldsa.ml proves correctness       *)
(* ------------------------------------------------------------------------- *)


(* ------------------------------------------------------------------------- *)
(* Main correctness goal (in g() form for interactive development).          *)
(* ------------------------------------------------------------------------- *)

(*** getting PC length/size:
let len_thm = REWRITE_CONV[mldsa_pointwise_tmc] `LENGTH mldsa_pointwise_tmc` in
let len_computed = LENGTH_CONV (rhs (concl len_thm)) in
let final_value = rhs (concl len_computed) in
dest_small_numeral final_value;;
***)

g(`!c a b qdata x y pc.
        aligned 32 c /\
        aligned 32 a /\
        aligned 32 b /\
        aligned 32 qdata /\
        ALL (nonoverlapping (c, 1024))
            [(word pc, 409); (a, 1024); (b, 1024); (qdata, 64)] /\
        ALL (nonoverlapping (a, 1024))
            [(word pc, 409); (b, 1024); (qdata, 64)] /\
        ALL (nonoverlapping (b, 1024))
            [(word pc, 409); (qdata, 64)] /\
        nonoverlapping (word pc, 409) (qdata, 64)
        ==> ensures x86
             (\s. bytes_loaded s (word pc) (BUTLAST mldsa_pointwise_tmc) /\
                  read RIP s = word pc /\
                  C_ARGUMENTS [c; a; b; qdata] s /\
                  (!i. i < 256 ==> abs(ival(x i)) <= &(9 * 8380417)) /\
                  (!i. i < 256 ==> abs(ival(y i)) <= &(9 * 8380417)) /\
                  (!i. i < 256
                       ==> read(memory :> bytes32(word_add a (word(4 * i)))) s =
                           x i) /\
                  (!i. i < 256
                       ==> read(memory :> bytes32(word_add b (word(4 * i)))) s =
                           y i))
             (\s. read RIP s = word(pc + 0x198) /\
                  (!i. i < 256
                       ==> read(memory :> bytes32(word_add c (word(4 * i)))) s =
                           mldsa_pointwise_mont
                             (read(memory :> bytes64 qdata) s,
                              read(memory :> bytes64(word_add qdata (word 32))) s)
                             (x i, y i)))
             (MAYCHANGE [RIP] ,, MAYCHANGE [events] ,,
              MAYCHANGE [ZMM0; ZMM1; ZMM2; ZMM3; ZMM4; ZMM5; ZMM6; ZMM7;
                         ZMM8; ZMM9; ZMM10; ZMM11; ZMM12; ZMM13; ZMM14; ZMM15] ,,
              MAYCHANGE [RAX] ,, MAYCHANGE SOME_FLAGS ,,
              MAYCHANGE [memory :> bytes(c, 1024)])`);;

e(REWRITE_TAC[NONOVERLAPPING_CLAUSES; ALL; C_ARGUMENTS; 
              fst MLDSA_POINTWISE_TMC_EXEC]);;

e(REPEAT STRIP_TAC);;

e(ENSURES_INIT_TAC "s0");;

e(MP_TAC(end_itlist CONJ (map (fun n -> READ_MEMORY_MERGE_CONV 3
    (subst[mk_small_numeral(32*n),`n:num`]
      `read (memory :> bytes256(word_add a (word n))) s0`))
    (0--31))));;

e(ASM_REWRITE_TAC[WORD_ADD_0]);;

e(DISCARD_MATCHING_ASSUMPTIONS [`read (memory :> bytes32 any) s = x`]);;

e(MP_TAC(end_itlist CONJ (map (fun n -> READ_MEMORY_MERGE_CONV 3
    (subst[mk_small_numeral(32*n),`n:num`]
      `read (memory :> bytes256(word_add b (word n))) s0`))
    (0--31))));;

(*** could add ***)
e(ASM_REWRITE_TAC[WORD_ADD_0]);;
e(DISCARD_MATCHING_ASSUMPTIONS [`read (memory :> bytes32 any) s = y`]);;
e(REPEAT STRIP_TAC);;
(*** end could add ***)

(*** so the simulation ***)
e(MAP_EVERY (fun n -> X86_STEPS_TAC MLDSA_POINTWISE_TMC_EXEC [n] THEN
                      SIMD_SIMPLIFY_TAC [mldsa_pointwise_mont])
            (1--543));;


e(ENSURES_FINAL_STATE_TAC THEN
  ASM_REWRITE_TAC[]);;

e(REPEAT(FIRST_X_ASSUM(STRIP_ASSUME_TAC o
  CONV_RULE(SIMD_SIMPLIFY_CONV[]) o
  CONV_RULE(READ_MEMORY_SPLIT_CONV 3) o
  check (can (term_match [] `read qqq s:int256 = xxx`) o concl))));;

e(CONV_TAC(TOP_DEPTH_CONV EXPAND_CASES_CONV) THEN
  CONV_TAC(DEPTH_CONV NUM_MULT_CONV THENC
           DEPTH_CONV NUM_ADD_CONV THENC
           DEPTH_CONV let_CONV) THEN
  ASM_REWRITE_TAC[WORD_ADD_0]);;

e(DISCARD_STATE_TAC "s543");;

e(REPEAT CONJ_TAC THEN
  REWRITE_TAC[mldsa_pointwise_mont]);;

e(ASSUM_LIST((fun ths -> W(MP_TAC o CONJUNCT1 o GEN_CONGBOUND_RULE ths o
    rand o lhand o rator o snd))) THEN
  REWRITE_TAC[GSYM INT_REM_EQ] THEN 
  CONV_TAC INT_REM_DOWN_CONV THEN
  MATCH_MP_TAC EQ_IMP THEN 
  AP_TERM_TAC THEN 
  AP_THM_TAC THEN 
  AP_TERM_TAC THEN
  CONV_TAC INT_RING);;

(*** 


e(ASSUM_LIST((fun ths -> W(MP_TAC o CONJUNCT1 o GEN_CONGBOUND_RULE ths o
    rand o lhand o rator o snd))));;

e(REWRITE_TAC[GSYM INT_REM_EQ]);;

e(CONV_TAC INT_REM_DOWN_CONV);;

e(MATCH_MP_TAC EQ_IMP);;

e(AP_TERM_TAC);;

e(AP_THM_TAC);;

e(AP_TERM_TAC);;

e(CONV_TAC INT_RING);;




e(X86_STEPS_TAC MLDSA_POINTWISE_TMC_EXEC (1--543));;
e(ENSURES_FINAL_STATE_TAC);;
e(ASM_REWRITE_TAC[]);;
e(CONJ_TAC);;

e(REWRITE_TAC[MAYCHANGE]);;
e(GEN_TAC THEN DISCH_TAC);;

e(ASM_REWRITE_TAC[ASSIGNS]);;

(* ========================================================================= *)
(* Full Proof Development with Loop Unrolling                                *)
(* ========================================================================= *)

(* After memory merging for inputs *)
(*
e(MP_TAC(end_itlist CONJ (map (fun n -> READ_MEMORY_MERGE_CONV 3
    (subst[mk_small_numeral(32*n),`n:num`]
      `read (memory :> bytes256(word_add a (word n))) s0`))
    (0--31))));;

e(ASM_REWRITE_TAC[WORD_ADD_0]);;
e(DISCARD_MATCHING_ASSUMPTIONS [`read (memory :> bytes32 any) s = x`]);;
  
e(MP_TAC(end_itlist CONJ (map (fun n -> READ_MEMORY_MERGE_CONV 3
    (subst[mk_small_numeral(32*n),`n:num`]
      `read (memory :> bytes256(word_add b (word n))) s0`))
    (0--31))));;

e(ASM_REWRITE_TAC[WORD_ADD_0]);;
e(DISCARD_MATCHING_ASSUMPTIONS [`read (memory :> bytes32 any) s = x`]);;
e(REPEAT STRIP_TAC);;
*)

(* After execution and ENSURES_FINAL_STATE_TAC *)
(*
(* Memory conversion: bytes256 writes -> bytes32 reads for output *)
e(REPEAT(FIRST_X_ASSUM(STRIP_ASSUME_TAC o
    CONV_RULE(SIMD_SIMPLIFY_CONV[]) o
    CONV_RULE(READ_MEMORY_SPLIT_CONV 3) o
    check (can (term_match [] `read qqq s:int256 = xxx`) o concl))));;

(* Final simplification *)
e(CONV_TAC(TOP_DEPTH_CONV EXPAND_CASES_CONV));;
e(CONV_TAC(DEPTH_CONV NUM_MULT_CONV THENC
           DEPTH_CONV NUM_ADD_CONV THENC
           DEPTH_CONV let_CONV));;
e(ASM_REWRITE_TAC[WORD_ADD_0]);;

e(DISCARD_STATE_TAC "s543");;

(* Prove correctness for each coefficient *)
e(REPEAT CONJ_TAC);;
e(REWRITE_TAC[pmul_montred_mldsa; pmontred_mldsa; pmul_mldsa]);;
e(STRIP_TAC);;
  
(* Bounds and congruence reasoning *)
e(ASSUM_LIST((fun ths -> W(MP_TAC o CONJUNCT1 o GEN_CONGBOUND_RULE ths o
    rand o lhand o rator o snd))));;
e(REWRITE_TAC[GSYM INT_REM_EQ]);;
e(CONV_TAC INT_REM_DOWN_CONV);;
e(MATCH_MP_TAC EQ_IMP);;
e(AP_TERM_TAC);;
e(AP_THM_TAC);;
e(AP_TERM_TAC);;
e(CONV_TAC INT_RING);;
*)
***)
