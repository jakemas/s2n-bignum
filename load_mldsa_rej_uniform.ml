(* Loader for mldsa_rej_uniform checkpoint.
   Run from s2n-bignum dir with HOLLIGHT_LOAD_PATH set to mldsa-native proofs/hol_light.
   This loads all dependencies and the machine code + helpers, stopping before the goal. *)

(* Base x86 infrastructure (from s2n-bignum, resolved via cwd) *)
needs "x86/proofs/base.ml";;

(* ML-DSA common specs (from mldsa-native, resolved via HOLLIGHT_LOAD_PATH) *)
needs "common/mldsa_specs.ml";;

(* Rejection uniform lookup table — no dependencies on proof lemmas *)
needs "x86_64/proofs/mldsa_rej_uniform_table.ml";;

(* === Lemmas that helpers file depends on === *)

let VPSUBD_SIGN_BIT_BOUNDED = prove
 (`!x:int32. val x < 8388608
     ==> (bit 31 (word_sub x (word 8380417)) <=> val x < 8380417)`,
  GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[BIT_VAL; DIMINDEX_32] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[VAL_WORD_SUB; DIMINDEX_32; VAL_WORD] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  ASM_CASES_TAC `val(x:int32) < 8380417` THEN ASM_REWRITE_TAC[] THENL
   [SUBGOAL_THEN
     `(val(x:int32) + 4286586879) MOD 4294967296 = val x + 4286586879`
    SUBST1_TAC THENL
     [MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC(MESON[ODD; ARITH_RULE `ODD 1`] `n = 1 ==> ODD n`) THEN
    MATCH_MP_TAC DIV_UNIQ THEN
    EXISTS_TAC `val(x:int32) + 2139103231` THEN ASM_ARITH_TAC;
    REWRITE_TAC[NOT_ODD] THEN
    SUBGOAL_THEN
     `(val(x:int32) + 4286586879) MOD 4294967296 = val x - 8380417`
    SUBST1_TAC THENL
     [SUBGOAL_THEN
       `val(x:int32) + 4286586879 = (val x - 8380417) + 1 * 4294967296`
      SUBST1_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[MOD_MULT_ADD] THEN MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    SIMP_TAC[DIV_LT; EVEN] THEN ASM_ARITH_TAC]);;

let SIGN_BIT_BITVAL = prove
 (`!x0:int32. val x0 < 8388608
   ==> bitval(bit 31 (word_sub x0 (word 8380417):int32)) = bitval(val x0 < 8380417)`,
  GEN_TAC THEN DISCH_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[BIT_VAL; DIMINDEX_32] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[VAL_WORD_SUB; DIMINDEX_32; VAL_WORD] THEN CONV_TAC NUM_REDUCE_CONV THEN
  ASM_CASES_TAC `val(x0:int32) < 8380417` THEN ASM_REWRITE_TAC[] THENL
   [SUBGOAL_THEN `(val(x0:int32) + 4286586879) MOD 4294967296 = val x0 + 4286586879` SUBST1_TAC THENL
     [MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC(MESON[ODD; ARITH_RULE `ODD 1`] `n = 1 ==> ODD n`) THEN
    MATCH_MP_TAC DIV_UNIQ THEN EXISTS_TAC `val(x0:int32) + 2139103231` THEN ASM_ARITH_TAC;
    SUBGOAL_THEN `(val(x0:int32) + 4286586879) MOD 4294967296 = val x0 - 8380417` SUBST1_TAC THENL
     [SUBGOAL_THEN `val(x0:int32) + 4286586879 = (val x0 - 8380417) + 1 * 4294967296` SUBST1_TAC THENL
       [ASM_ARITH_TAC; REWRITE_TAC[MOD_MULT_ADD] THEN MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC];
      REWRITE_TAC[NOT_ODD] THEN SIMP_TAC[DIV_LT; EVEN] THEN ASM_ARITH_TAC]]);;

(* NOW load helpers — they depend on VPSUBD_SIGN_BIT_BOUNDED and SIGN_BIT_BITVAL *)
needs "x86_64/proofs/mldsa_rej_uniform_helpers.ml";;

(* Machine code definition — use absolute path since cwd is s2n-bignum *)
let hollight_load_path =
  try Sys.getenv "HOLLIGHT_LOAD_PATH" with Not_found -> ".";;

let mldsa_rej_uniform_mc = define_assert_from_elf
  "mldsa_rej_uniform_mc"
  (Filename.concat hollight_load_path "x86_64/mldsa/mldsa_rej_uniform.o")
[
  0xf3; 0x0f; 0x1e; 0xfa;
  0x49; 0xba; 0x00; 0x01; 0x02; 0xff; 0x03; 0x04; 0x05; 0xff;
  0xc4; 0xc1; 0xf9; 0x6e; 0xc2;
  0x49; 0xba; 0x06; 0x07; 0x08; 0xff; 0x09; 0x0a; 0x0b; 0xff;
  0xc4; 0xc3; 0xf9; 0x22; 0xc2; 0x01;
  0x49; 0xba; 0x04; 0x05; 0x06; 0xff; 0x07; 0x08; 0x09; 0xff;
  0xc4; 0xc1; 0xf9; 0x6e; 0xda;
  0x49; 0xba; 0x0a; 0x0b; 0x0c; 0xff; 0x0d; 0x0e; 0x0f; 0xff;
  0xc4; 0xc3; 0xe1; 0x22; 0xda; 0x01;
  0xc4; 0xe3; 0x7d; 0x38; 0xc3; 0x01;
  0x41; 0xb8; 0xff; 0xff; 0x7f; 0x00;
  0xc4; 0xc1; 0x79; 0x6e; 0xc8;
  0xc4; 0xe2; 0x7d; 0x58; 0xc9;
  0x41; 0xb8; 0x01; 0xe0; 0x7f; 0x00;
  0xc4; 0xc1; 0x79; 0x6e; 0xd0;
  0xc4; 0xe2; 0x7d; 0x58; 0xd2;
  0x31; 0xc0;
  0x31; 0xc9;
  0x3d; 0xf8; 0x00; 0x00; 0x00;
  0x77; 0x46;
  0x81; 0xf9; 0x28; 0x03; 0x00; 0x00;
  0x77; 0x3e;
  0xc5; 0xfe; 0x6f; 0x1c; 0x0e;
  0x83; 0xc1; 0x18;
  0xc4; 0xe3; 0xfd; 0x00; 0xdb; 0x94;
  0xc4; 0xe2; 0x65; 0x00; 0xd8;
  0xc5; 0xe5; 0xdb; 0xd9;
  0xc5; 0xe5; 0xfa; 0xe2;
  0xc5; 0x7c; 0x50; 0xc4;
  0xf3; 0x45; 0x0f; 0xb8; 0xc8;
  0xc4; 0xa1; 0x7a; 0x7e; 0x24; 0xc2;
  0xc4; 0xe2; 0x7d; 0x31; 0xe4;
  0xc4; 0xe2; 0x5d; 0x36; 0xdb;
  0xc5; 0xfe; 0x7f; 0x1c; 0x87;
  0x44; 0x01; 0xc8;
  0xeb; 0xb3;
  0x3d; 0x00; 0x01; 0x00; 0x00;
  0x73; 0x36;
  0x81; 0xf9; 0x45; 0x03; 0x00; 0x00;
  0x77; 0x2e;
  0x44; 0x0f; 0xb7; 0x04; 0x0e;
  0x44; 0x0f; 0xb6; 0x4c; 0x0e; 0x02;
  0x41; 0xc1; 0xe1; 0x10;
  0x45; 0x09; 0xc8;
  0x41; 0x81; 0xe0; 0xff; 0xff; 0x7f; 0x00;
  0x83; 0xc1; 0x03;
  0x41; 0x81; 0xf8; 0x01; 0xe0; 0x7f; 0x00;
  0x73; 0xcc;
  0x44; 0x89; 0x04; 0x87;
  0x83; 0xc0; 0x01;
  0xeb; 0xc3;
  0xc5; 0xf8; 0x77;
  0xc3
];;

let mldsa_rej_uniform_tmc =
  define_trimmed "mldsa_rej_uniform_tmc" mldsa_rej_uniform_mc;;

let MLDSA_REJ_UNIFORM_EXEC = X86_MK_CORE_EXEC_RULE mldsa_rej_uniform_tmc;;

(* Remaining helper lemmas from the proof file *)

let DIMINDEX_23 = DIMINDEX_CONV `dimindex(:23)`;;
let DIMINDEX_24 = DIMINDEX_CONV `dimindex(:24)`;;

let VAL_MOD_23_EQ_AND = prove
 (`!w:24 word. (word(val w MOD 2 EXP 23):int32) =
               word_and (word_zx w:int32) (word 8388607)`,
  GEN_TAC THEN CONV_TAC WORD_BLAST);;

let REJ_SAMPLE = define
 `REJ_SAMPLE l = FILTER (\x:int32. val x < 8380417)
    (MAP (\x:24 word. word(val x MOD 2 EXP 23):int32) l)`;;

let REJ_SAMPLE_EMPTY = prove
 (`REJ_SAMPLE [] = []`,
  REWRITE_TAC[REJ_SAMPLE; FILTER; MAP]);;

let REJ_SAMPLE_APPEND = prove
 (`!l1 l2. REJ_SAMPLE(APPEND l1 l2) =
           APPEND (REJ_SAMPLE l1) (REJ_SAMPLE l2)`,
  REWRITE_TAC[REJ_SAMPLE; MAP_APPEND; FILTER_APPEND]);;

let mldsa_mask_lemma = prove
 ((rand o concl o (EXPAND_CASES_CONV THENC NUM_REDUCE_CONV))
  `!i. i < 8
       ==> word_and (word_subword (q:int256) (32*i,32)) (word 8388607):int32 =
           word_zx(word_subword (q:int256) (32*i,23):23 word)`,
  CONV_TAC WORD_BLAST);;

let VAL_WORD_ZX_23 = prove
 (`!w:23 word. val(word_zx w:int32) < 8388608`,
  GEN_TAC THEN REWRITE_TAC[VAL_WORD_ZX_GEN; DIMINDEX_23; DIMINDEX_32] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  MP_TAC(ISPEC `w:23 word` VAL_BOUND) THEN
  REWRITE_TAC[DIMINDEX_23] THEN CONV_TAC NUM_REDUCE_CONV THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `val(w:23 word) MOD 4294967296 = val w` SUBST1_TAC THENL
   [MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC; ASM_ARITH_TAC]);;

let ODD_ADD_2 = prove
 (`!n. ODD(2 + n) <=> ODD n`,
  REWRITE_TAC[ODD_ADD] THEN CONV_TAC NUM_REDUCE_CONV);;

let COEFF_FROM_BYTES = prove
 ((rand o concl o (EXPAND_CASES_CONV THENC NUM_REDUCE_CONV))
  `!j. j < 8 ==>
    word_and (word_zx(word_subword (buf:192 word) (24*j,24):24 word):int32)
             (word 8388607) =
    word_zx(word_subword (buf:192 word) (24*j,23):23 word)`,
  CONV_TAC WORD_BLAST);;

Printf.printf "=== mldsa_rej_uniform checkpoint ready ===\n";;
Printf.printf "All dependencies loaded. Set your goal and go.\n";;
