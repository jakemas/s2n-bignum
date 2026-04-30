(*
 * Copyright (c) The mldsa-native project authors
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* ML-DSA Rejection uniform sampling (x86_64 AVX2).                         *)
(*                                                                           *)
(* ML-DSA uses q = 8380417 with 23-bit coefficients packed as 3 bytes each. *)
(* The AVX2 assembly processes 24 bytes (8 coefficients) per main-loop      *)
(* iteration via VPERMQ+VPSHUFB extraction, VPAND masking, VPSUBD+VMOVMSKPS *)
(* rejection, and VPERMD+table compaction. A scalar tail handles remaining   *)
(* bytes. Stores go directly to the output buffer (no stack buffer).         *)
(* ========================================================================= *)

needs "x86/proofs/base.ml";;
needs "common/mldsa_specs.ml";;
needs "x86_64/proofs/mldsa_rej_uniform_table.ml";;
needs "x86_64/proofs/mldsa_rej_uniform_helpers.ml";;

(*** print_literal_from_elf "x86_64/mldsa/mldsa_rej_uniform.o";;
 ***)

let mldsa_rej_uniform_mc = define_assert_from_elf
  "mldsa_rej_uniform_mc" "x86_64/mldsa/mldsa_rej_uniform.o"
(*** BYTECODE START ***)
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
(*** BYTECODE END ***)

let mldsa_rej_uniform_tmc =
  define_trimmed "mldsa_rej_uniform_tmc" mldsa_rej_uniform_mc;;

let MLDSA_REJ_UNIFORM_EXEC = X86_MK_CORE_EXEC_RULE mldsa_rej_uniform_tmc;;

(* ------------------------------------------------------------------------- *)
(* Helper lemmas                                                             *)
(* ------------------------------------------------------------------------- *)

let DIMINDEX_23 = DIMINDEX_CONV `dimindex(:23)`;;
let DIMINDEX_24 = DIMINDEX_CONV `dimindex(:24)`;;

let VAL_MOD_23_EQ_AND = prove
 (`!w:24 word. (word(val w MOD 2 EXP 23):int32) =
               word_and (word_zx w:int32) (word 8388607)`,
  GEN_TAC THEN CONV_TAC WORD_BLAST);;

(* Uncomment for debugging: x86_print_log := true;; components_print_log := true;; *)

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

(* VPAND 0x7FFFFF extracts 23-bit subwords from all 8 lanes *)
let mldsa_mask_lemma = prove
 ((rand o concl o (EXPAND_CASES_CONV THENC NUM_REDUCE_CONV))
  `!i. i < 8
       ==> word_and (word_subword (q:int256) (32*i,32)) (word 8388607):int32 =
           word_zx(word_subword (q:int256) (32*i,23):23 word)`,
  CONV_TAC WORD_BLAST);;

(* Zero-extended 23-bit words have val < 2^23 *)
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

(* Sign bit of (x - Q) detects rejection when val x < 2^23 *)
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

(* Byte extraction from 192-bit = 23-bit subword extraction *)
let COEFF_FROM_BYTES = prove
 ((rand o concl o (EXPAND_CASES_CONV THENC NUM_REDUCE_CONV))
  `!j. j < 8 ==>
    word_and (word_zx(word_subword (buf:192 word) (24*j,24):24 word):int32)
             (word 8388607) =
    word_zx(word_subword (buf:192 word) (24*j,23):23 word)`,
  CONV_TAC WORD_BLAST);;

(* Sign bit of (x - Q) equals rejection bitval when val x < 2^23 *)
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

(* POPCNT of VMOVMSKPS sign-bit mask = LENGTH(FILTER) — 256-case brute force *)
let POPCNT_EQ_LENGTH_FILTER = prove
 (`!x0 x1 x2 x3 x4 x5 x6 x7:int32.
   val x0 < 8388608 /\ val x1 < 8388608 /\ val x2 < 8388608 /\ val x3 < 8388608 /\
   val x4 < 8388608 /\ val x5 < 8388608 /\ val x6 < 8388608 /\ val x7 < 8388608
   ==> word_popcount(word(
         bitval(bit 31 (word_sub x0 (word 8380417):int32)) +
         2 * bitval(bit 31 (word_sub x1 (word 8380417):int32)) +
         4 * bitval(bit 31 (word_sub x2 (word 8380417):int32)) +
         8 * bitval(bit 31 (word_sub x3 (word 8380417):int32)) +
         16 * bitval(bit 31 (word_sub x4 (word 8380417):int32)) +
         32 * bitval(bit 31 (word_sub x5 (word 8380417):int32)) +
         64 * bitval(bit 31 (word_sub x6 (word 8380417):int32)) +
         128 * bitval(bit 31 (word_sub x7 (word 8380417):int32))):byte) =
       LENGTH(FILTER (\x:int32. val x < 8380417) [x0;x1;x2;x3;x4;x5;x6;x7])`,
  REPEAT STRIP_TAC THEN
  REPEAT(FIRST_X_ASSUM(fun th ->
    try let th' = MATCH_MP SIGN_BIT_BITVAL th in REWRITE_TAC[th'] with _ -> ASSUME_TAC th)) THEN
  MAP_EVERY ASM_CASES_TAC
   [`val(x0:int32) < 8380417`; `val(x1:int32) < 8380417`;
    `val(x2:int32) < 8380417`; `val(x3:int32) < 8380417`;
    `val(x4:int32) < 8380417`; `val(x5:int32) < 8380417`;
    `val(x6:int32) < 8380417`; `val(x7:int32) < 8380417`] THEN
  ASM_REWRITE_TAC[FILTER; bitval; LENGTH] THEN
  CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV));;

(* LENGTH(FILTER) = sum of bitvals — the 256-case brute force *)
let FILTER_LENGTH_8 = prove
 (`!x0 x1 x2 x3 x4 x5 x6 x7:int32.
   val x0 < 8388608 /\ val x1 < 8388608 /\ val x2 < 8388608 /\ val x3 < 8388608 /\
   val x4 < 8388608 /\ val x5 < 8388608 /\ val x6 < 8388608 /\ val x7 < 8388608
   ==> LENGTH(FILTER (\x. val x < 8380417) [x0;x1;x2;x3;x4;x5;x6;x7]) =
       bitval(val x0 < 8380417) + bitval(val x1 < 8380417) +
       bitval(val x2 < 8380417) + bitval(val x3 < 8380417) +
       bitval(val x4 < 8380417) + bitval(val x5 < 8380417) +
       bitval(val x6 < 8380417) + bitval(val x7 < 8380417)`,
  REPEAT STRIP_TAC THEN
  MAP_EVERY ASM_CASES_TAC
   [`val(x0:int32) < 8380417`; `val(x1:int32) < 8380417`;
    `val(x2:int32) < 8380417`; `val(x3:int32) < 8380417`;
    `val(x4:int32) < 8380417`; `val(x5:int32) < 8380417`;
    `val(x6:int32) < 8380417`; `val(x7:int32) < 8380417`] THEN
  ASM_REWRITE_TAC[FILTER; LENGTH; bitval] THEN
  CONV_TAC NUM_REDUCE_CONV);;

(* REJ_SAMPLE splits across a single 8-coefficient iteration *)
let REJ_SAMPLE_ITERATION = prove
 (`!inlist i.
    8 * (i + 1) <= LENGTH inlist
    ==> REJ_SAMPLE(SUB_LIST(0,8*(i+1)) inlist) =
        APPEND (REJ_SAMPLE(SUB_LIST(0,8*i) inlist))
               (REJ_SAMPLE(SUB_LIST(8*i,8) inlist))`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[ARITH_RULE `8*(i+1) = 8*i + 8`] THEN
  MP_TAC(ISPECL [`inlist:(24 word)list`; `8 * i`; `8`; `0`] SUB_LIST_SPLIT) THEN
  REWRITE_TAC[ADD_CLAUSES] THEN
  DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[REJ_SAMPLE_APPEND]);;

(* VMOVMSKPS sign bits + POPCNT = LENGTH(FILTER) for 8 dword lanes *)
let POPCNT_VMOVMSKPS_LEMMA = prove
 (`!q:int256.
  word_popcount(word(
    bitval(bit 31 (word_sub (word_subword (word_and q (word 226156397384342666605459106258636701594091082888230722833791023177481060351):int256) (0,32):int32) (word 8380417):int32)) +
    2 * bitval(bit 31 (word_sub (word_subword (word_and q (word 226156397384342666605459106258636701594091082888230722833791023177481060351):int256) (32,32):int32) (word 8380417):int32)) +
    4 * bitval(bit 31 (word_sub (word_subword (word_and q (word 226156397384342666605459106258636701594091082888230722833791023177481060351):int256) (64,32):int32) (word 8380417):int32)) +
    8 * bitval(bit 31 (word_sub (word_subword (word_and q (word 226156397384342666605459106258636701594091082888230722833791023177481060351):int256) (96,32):int32) (word 8380417):int32)) +
    16 * bitval(bit 31 (word_sub (word_subword (word_and q (word 226156397384342666605459106258636701594091082888230722833791023177481060351):int256) (128,32):int32) (word 8380417):int32)) +
    32 * bitval(bit 31 (word_sub (word_subword (word_and q (word 226156397384342666605459106258636701594091082888230722833791023177481060351):int256) (160,32):int32) (word 8380417):int32)) +
    64 * bitval(bit 31 (word_sub (word_subword (word_and q (word 226156397384342666605459106258636701594091082888230722833791023177481060351):int256) (192,32):int32) (word 8380417):int32)) +
    128 * bitval(bit 31 (word_sub (word_subword (word_and q (word 226156397384342666605459106258636701594091082888230722833791023177481060351):int256) (224,32):int32) (word 8380417):int32))):byte) =
  LENGTH(FILTER (\c:int32. val c < 8380417)
    [word_subword (word_and q (word 226156397384342666605459106258636701594091082888230722833791023177481060351):int256) (0,32):int32;
     word_subword (word_and q (word 226156397384342666605459106258636701594091082888230722833791023177481060351):int256) (32,32);
     word_subword (word_and q (word 226156397384342666605459106258636701594091082888230722833791023177481060351):int256) (64,32);
     word_subword (word_and q (word 226156397384342666605459106258636701594091082888230722833791023177481060351):int256) (96,32);
     word_subword (word_and q (word 226156397384342666605459106258636701594091082888230722833791023177481060351):int256) (128,32);
     word_subword (word_and q (word 226156397384342666605459106258636701594091082888230722833791023177481060351):int256) (160,32);
     word_subword (word_and q (word 226156397384342666605459106258636701594091082888230722833791023177481060351):int256) (192,32);
     word_subword (word_and q (word 226156397384342666605459106258636701594091082888230722833791023177481060351):int256) (224,32)])`,
  GEN_TAC THEN REWRITE_TAC[WORD_SUBWORD_AND] THEN
  CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV) THEN
  REWRITE_TAC[mldsa_mask_lemma] THEN
  MATCH_MP_TAC POPCNT_EQ_LENGTH_FILTER THEN
  REWRITE_TAC[VAL_WORD_ZX_23]);;

(* Full iteration bridge: split, length, and bound *)
let SIMD_ITERATION_BRIDGE = prove
 (`!inlist:(24 word)list i curlist curlen.
    REJ_SAMPLE(SUB_LIST(0,8*i) inlist) = curlist /\
    LENGTH curlist = curlen /\
    8*(i+1) <= LENGTH inlist
    ==> REJ_SAMPLE(SUB_LIST(0,8*(i+1)) inlist) =
        APPEND curlist (REJ_SAMPLE(SUB_LIST(8*i,8) inlist)) /\
        LENGTH(REJ_SAMPLE(SUB_LIST(0,8*(i+1)) inlist)) =
        curlen + LENGTH(REJ_SAMPLE(SUB_LIST(8*i,8) inlist)) /\
        LENGTH(REJ_SAMPLE(SUB_LIST(8*i,8) inlist)) <= 8`,
  REPEAT STRIP_TAC THENL
   [REWRITE_TAC[ARITH_RULE `8*(i+1) = 8*i + 8`] THEN
    MP_TAC(ISPECL [`inlist:(24 word)list`; `8*i`; `8`; `0`] SUB_LIST_SPLIT) THEN
    REWRITE_TAC[ADD_CLAUSES] THEN DISCH_THEN SUBST1_TAC THEN
    ASM_REWRITE_TAC[REJ_SAMPLE_APPEND];
    REWRITE_TAC[ARITH_RULE `8*(i+1) = 8*i + 8`] THEN
    MP_TAC(ISPECL [`inlist:(24 word)list`; `8*i`; `8`; `0`] SUB_LIST_SPLIT) THEN
    REWRITE_TAC[ADD_CLAUSES] THEN DISCH_THEN SUBST1_TAC THEN
    ASM_REWRITE_TAC[REJ_SAMPLE_APPEND; LENGTH_APPEND];
    REWRITE_TAC[REJ_SAMPLE] THEN
    W(MP_TAC o PART_MATCH lhand LENGTH_FILTER o lhand o snd) THEN
    MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] LE_TRANS) THEN
    REWRITE_TAC[LENGTH_MAP; LENGTH_SUB_LIST] THEN ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* JA branch resolution tactics.                                             *)
(*                                                                           *)
(* The SIMD loop has two JA (jump if above) instructions:                    *)
(*   CMP eax, 0xF8; JA scalar    -- if outlen > 248, exit SIMD loop         *)
(*   CMP ecx, 0x328; JA scalar   -- if byte offset > 808, exit SIMD loop    *)
(* Inside the loop body we know these are NOT taken (WOP guarantees).        *)
(* RESOLVE_JA_ONLY_TAC replaces the conditional RIP hypothesis.              *)
(* RESOLVE_JA_CURLEN_TAC/RESOLVE_JA_OFFSET_TAC prove ~p for the condition.  *)
(* IMPORTANT: no ASM_* tactics here to avoid hypothesis pollution.           *)
(* ------------------------------------------------------------------------- *)

let RESOLVE_JA_ONLY_TAC svar =
  fun th ->
    TRY(FIRST_X_ASSUM(K ALL_TAC o check (fun th' ->
      let c = concl th' in
      is_eq c && can (find_term is_cond) c &&
      can (find_term ((=) svar)) c &&
      can (find_term ((=) `RIP`)) c))) THEN
    ASSUME_TAC th;;

let RESOLVE_JA_CURLEN_TAC =
  FIRST_X_ASSUM(SUBST1_TAC o check (fun th ->
    can (find_term ((=) `RIP`)) (concl th) && is_eq(concl th) &&
    can (find_term is_cond) (concl th))) THEN
  MATCH_MP_TAC(TAUT `~p ==> (if p then a else b) = b`) THEN
  REWRITE_TAC[NOT_CLAUSES; DE_MORGAN_THM;
              VAL_WORD_ZX_GEN; VAL_WORD_SUB_CASES; VAL_WORD;
              DIMINDEX_32; DIMINDEX_64] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[REAL_EQ_SUB_RADD; REAL_OF_NUM_ADD; REAL_OF_NUM_EQ] THEN
  UNDISCH_TAC `curlen <= 248` THEN ARITH_TAC;;

let RESOLVE_JA_OFFSET_TAC =
  FIRST_X_ASSUM(SUBST1_TAC o check (fun th ->
    can (find_term ((=) `RIP`)) (concl th) && is_eq(concl th) &&
    can (find_term is_cond) (concl th))) THEN
  MATCH_MP_TAC(TAUT `~p ==> (if p then a else b) = b`) THEN
  REWRITE_TAC[NOT_CLAUSES; DE_MORGAN_THM;
              VAL_WORD_ZX_GEN; VAL_WORD_SUB_CASES; VAL_WORD;
              DIMINDEX_32; DIMINDEX_64] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[REAL_EQ_SUB_RADD; REAL_OF_NUM_ADD; REAL_OF_NUM_EQ] THEN
  UNDISCH_TAC `24 * i <= 808` THEN ARITH_TAC;;

(* ------------------------------------------------------------------------- *)
(* The main correctness theorem.                                             *)
(*                                                                           *)
(* Proved structure:                                                         *)
(*   Phase 1: WOP (808/248 thresholds) to find loop count N                  *)
(*   Phase 2: ENSURES_WHILE_UP2_TAC for SIMD loop                           *)
(*     Subgoal 1: Pre-loop (instrs 1-17) — FULLY PROVED                     *)
(*     Subgoal 2: Loop body — JA resolution + SIMD simulation proved,       *)
(*                semantic proof (256-case brute force) uses CHEAT_TAC       *)
(*     Subgoal 3: Post-loop — CHEAT_TAC (scalar loop + VZEROUPPER + RET)    *)
(* ------------------------------------------------------------------------- *)

let unsolved_vpermd = ref (None : goal option);;

let MLDSA_REJ_UNIFORM_CORRECT = prove
 (`!res buf table (inlist:(24 word)list) pc stackpointer.
    LENGTH inlist = 280 /\
    nonoverlapping (word pc, 246) (res, 1024) /\
    nonoverlapping (word pc, 246) (buf, 840) /\
    nonoverlapping (word pc, 246) (table, 2048) /\
    nonoverlapping (res, 1024) (buf, 840) /\
    nonoverlapping (res, 1024) (table, 2048) /\
    nonoverlapping (stackpointer, 8) (res, 1024)
    ==> ensures x86
         (\s. bytes_loaded s (word pc) (BUTLAST mldsa_rej_uniform_tmc) /\
              read RIP s = word pc /\
              read RSP s = stackpointer /\
              C_ARGUMENTS [res; buf; table] s /\
              read(memory :> bytes(buf,840)) s = num_of_wordlist inlist /\
              read(memory :> bytes(table,2048)) s =
                num_of_wordlist(mldsa_rej_uniform_table:byte list))
         (\s. read RIP s = word(pc + 245) /\
              let outlist = SUB_LIST(0,256) (REJ_SAMPLE inlist) in
              let outlen = LENGTH outlist in
              C_RETURN s = word outlen /\
              read(memory :> bytes(res,4 * outlen)) s =
                num_of_wordlist outlist)
         (MAYCHANGE [RSP; RIP; RAX; RCX; R8; R9; R10] ,,
          MAYCHANGE [ZMM0; ZMM1; ZMM2; ZMM3; ZMM4;
                     ZMM5; ZMM6; ZMM7; ZMM8; ZMM9; ZMM10; ZMM11;
                     ZMM12; ZMM13; ZMM14; ZMM15] ,,
          MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
          MAYCHANGE [memory :> bytes(res,1024)])`,

  MAP_EVERY X_GEN_TAC
   [`res:int64`; `buf:int64`; `table:int64`;
    `inlist:(24 word)list`; `pc:num`;
    `stackpointer:int64`] THEN
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS; NONOVERLAPPING_CLAUSES] THEN
  STRIP_TAC THEN

  (* =================================================================== *)
  (* Phase 1: WOP to find loop iteration count N.                        *)
  (*                                                                     *)
  (* Thresholds 808/248 match the CMP instructions:                      *)
  (*   CMP eax, 0xF8 (248): JA exits if outlen > 248                    *)
  (*   CMP ecx, 0x328 (808): JA exits if offset > 808                   *)
  (* At m < N, negation gives: 24*(m+1) <= 832 /\ LENGTH(...) <= 248    *)
  (* IMPORTANT: use DISCH_THEN to avoid global NOT_LT rewrite.          *)
  (* =================================================================== *)

  SUBGOAL_THEN
   `?i. 832 < 24 * (i + 1) \/ 248 < LENGTH(REJ_SAMPLE(SUB_LIST(0,8 * i) inlist))`
  MP_TAC THENL
   [EXISTS_TAC `280:num` THEN ARITH_TAC;
    GEN_REWRITE_TAC LAND_CONV [num_WOP]] THEN
  DISCH_THEN(X_CHOOSE_THEN `N:num` (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  DISCH_THEN(fun th -> ASSUME_TAC(REWRITE_RULE[DE_MORGAN_THM; NOT_LT] th)) THEN
  SUBGOAL_THEN `~(N = 0)` ASSUME_TAC THENL
   [DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o check (is_disj o concl)) THEN
    ASM_REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES; SUB_LIST_CLAUSES] THEN
    REWRITE_TAC[REJ_SAMPLE_EMPTY; LENGTH] THEN ARITH_TAC;
    ALL_TAC] THEN

  (* =================================================================== *)
  (* Phase 2: ENSURES_WHILE_UP2_TAC for the SIMD loop.                  *)
  (*                                                                     *)
  (* Loop head: pc+104 (instruction 18: CMP eax,0xF8)                   *)
  (* Loop exit: pc+181 (instruction 36: scalar section entry)            *)
  (* UP2 automatically adds bytes_loaded to the invariant.               *)
  (* Bounds are derived from WOP inside the loop body, not stored.       *)
  (* =================================================================== *)

  ENSURES_WHILE_UP2_TAC `N:num` `pc + 104` `pc + 181`
   `\i s.
          read RSP s = stackpointer /\
          read (memory :> bytes (buf,840)) s = num_of_wordlist inlist /\
          read (memory :> bytes (table,2048)) s =
            num_of_wordlist(mldsa_rej_uniform_table:byte list) /\
          read RDI s = res /\ read RSI s = buf /\ read RDX s = table /\
          read YMM0 s =
            word 115366376096492355175489748997433888275274855593258845241081954797768348401920 /\
          read YMM1 s =
            word 226156397384342666605459106258636701594091082888230722833791023177481060351 /\
          read YMM2 s =
            word 225935595421087293402315996791205668696012104344015382954355885915737415681 /\
          let outlist = REJ_SAMPLE(SUB_LIST(0,8*i) inlist) in
          let outlen = LENGTH outlist in
          read RAX s = word outlen /\
          read RCX s = word(24*i) /\
          read(memory :> bytes(res,4*outlen)) s = num_of_wordlist outlist` THEN
  ASM_REWRITE_TAC[LT_REFL] THEN REPEAT CONJ_TAC THENL

   [(* ================================================================= *)
    (* Subgoal 1: Pre-loop setup (instructions 1-17, pc -> pc+104)       *)
    (* FULLY PROVED                                                      *)
    (* ================================================================= *)
    ENSURES_INIT_TAC "s0" THEN
    X86_STEPS_TAC MLDSA_REJ_UNIFORM_EXEC (1--17) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
    REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES; SUB_LIST_CLAUSES; REJ_SAMPLE_EMPTY;
                LENGTH; num_of_wordlist] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_MEMORY_BYTES_TRIVIAL] THEN
    CONV_TAC WORD_REDUCE_CONV;

    (* ================================================================= *)
    (* Subgoal 2: Loop body preservation (i -> i+1)                      *)
    (*                                                                   *)
    (* Structure:                                                        *)
    (*   (a) Derive bounds from WOP: curlen <= 248, 24*i <= 808          *)
    (*   (b) Simulate CMP+JA (instrs 18-19): resolve JA not taken       *)
    (*   (c) Simulate CMP+JA (instrs 20-21): resolve JA not taken       *)
    (*   (d) Simulate SIMD body (instrs 22-35)                           *)
    (*   (e) COND_CASES_TAC on i+1 < N                                  *)
    (*   (f) Semantic proof: relate SIMD to REJ_SAMPLE                   *)
    (* ================================================================= *)

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN

    ABBREV_TAC `curlist = REJ_SAMPLE (SUB_LIST(0,8*i) inlist)` THEN
    ABBREV_TAC `curlen = LENGTH(curlist:int32 list)` THEN
    CONV_TAC(RATOR_CONV(LAND_CONV(TOP_DEPTH_CONV let_CONV))) THEN
    ASM_REWRITE_TAC[] THEN

    (* (a) Get bounds from WOP at i *)
    FIRST_ASSUM(MP_TAC o C MATCH_MP (ASSUME `i:num < N`) o
      check (fun th -> is_forall(concl th))) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN

    SUBGOAL_THEN `curlen <= 248` ASSUME_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `24 * i <= 808` ASSUME_TAC THENL
     [UNDISCH_TAC `24 * (i + 1) <= 832` THEN ARITH_TAC; ALL_TAC] THEN

    ENSURES_INIT_TAC "s0" THEN

    (* (b) Instructions 18-19: CMP eax,0xF8; JA — not taken *)
    X86_STEPS_TAC MLDSA_REJ_UNIFORM_EXEC [18;19] THEN
    SUBGOAL_THEN `read RIP s19 = word(pc + 111):int64`
      (RESOLVE_JA_ONLY_TAC `s19:x86state`) THENL
     [RESOLVE_JA_CURLEN_TAC; ALL_TAC] THEN

    (* (c) Instructions 20-21: CMP ecx,0x328; JA — not taken *)
    X86_STEPS_TAC MLDSA_REJ_UNIFORM_EXEC [20;21] THEN
    SUBGOAL_THEN `read RIP s21 = word(pc + 119):int64`
      (RESOLVE_JA_ONLY_TAC `s21:x86state`) THENL
     [RESOLVE_JA_OFFSET_TAC; ALL_TAC] THEN

    (* (d) SIMD body: all verbose to preserve VMOVDQU→VPSHUFB→VPAND chain *)
    X86_VSTEPS_TAC MLDSA_REJ_UNIFORM_EXEC (22--29) THEN

    (* Abbreviate the 8 masked coefficients from YMM3 after VPAND *)
    (* Semantic bridge: use POPCNT_VMOVMSKPS_LEMMA to establish
       R9 = word(LENGTH(FILTER)) for the 8 masked dword lanes.
       The YMM3 at s26 = word_and(read YMM3 s25)(mask_broadcast).
       After ASM_REWRITE, the read R9 s29 expands to the popcount
       of the sign-bit mask, and the LEMMA matches directly. *)
    SUBGOAL_THEN
     `read R9 s29:int64 =
      word(LENGTH(FILTER (\c:int32. val c < 8380417)
        [word_subword (read YMM3 s26:int256) (0,32):int32;
         word_subword (read YMM3 s26) (32,32);
         word_subword (read YMM3 s26) (64,32);
         word_subword (read YMM3 s26) (96,32);
         word_subword (read YMM3 s26) (128,32);
         word_subword (read YMM3 s26) (160,32);
         word_subword (read YMM3 s26) (192,32);
         word_subword (read YMM3 s26) (224,32)]))`
    MP_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      CONV_TAC(LAND_CONV(REWR_CONV word_zx)) THEN
      REWRITE_TAC[VAL_WORD; DIMINDEX_32] THEN
      CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN
      AP_TERM_TAC THEN
      REPEAT(FIRST_X_ASSUM(K ALL_TAC o check (fun th ->
        can (find_term ((=) `s25:x86state`)) (concl th) ||
        can (find_term ((=) `s26:x86state`)) (concl th) ||
        can (find_term ((=) `s27:x86state`)) (concl th) ||
        can (find_term ((=) `s28:x86state`)) (concl th) ||
        can (find_term ((=) `s29:x86state`)) (concl th)))) THEN
      SIMP_TAC[WORD_ZX_ZX; DIMINDEX_32; DIMINDEX_64;
               ARITH_RULE `32 <= 64`] THEN
      SIMP_TAC[WORD_POPCOUNT_WORD_ZX; DIMINDEX_8; DIMINDEX_32;
               ARITH_RULE `8 <= 32`] THEN
      REWRITE_TAC[VMOVMSKPS_POPCOUNT_EQ; BIT_NESTED_JOIN_8] THEN
      REWRITE_TAC[POPCNT_VMOVMSKPS_LEMMA] THEN
      MATCH_MP_TAC MOD_LT THEN
      TRANS_TAC LTE_TRANS `9` THEN CONJ_TAC THENL
       [MATCH_MP_TAC(ARITH_RULE `n <= 8 ==> n < 9`) THEN
        W(MP_TAC o PART_MATCH lhand LENGTH_FILTER o lhand o snd) THEN
        REWRITE_TAC[LENGTH] THEN ARITH_TAC;
        ARITH_TAC];
      DISCARD_MATCHING_ASSUMPTIONS [`read R9 s = x`] THEN STRIP_TAC] THEN

    (* SIMD↔spec: prove BEFORE DISCARD while YMM3/buffer hyps available.
       newlen (the FILTER length over SIMD coefficients) = LENGTH(REJ_SAMPLE(...))
       This is the key semantic bridge: VPERMQ+VPSHUFB+VPAND = spec's MAP+FILTER.
       The result is state-independent and survives DISCARD_OLDSTATE_TAC.
       Approach: WORD_SIMPLE_SUBWORD_CONV reduces the 256-bit VPSHUFB chain
       to clean 8-bit byte extractions from the bytes256 memory read. Then
       bytes256 → bytes(32) → MOD 2^192 → num_of_wordlist(SUB_LIST). *)
    SUBGOAL_THEN
     `FILTER (\c:int32. val c < 8380417)
        [word_subword (read YMM3 s26:int256) (0,32):int32;
         word_subword (read YMM3 s26) (32,32);
         word_subword (read YMM3 s26) (64,32);
         word_subword (read YMM3 s26) (96,32);
         word_subword (read YMM3 s26) (128,32);
         word_subword (read YMM3 s26) (160,32);
         word_subword (read YMM3 s26) (192,32);
         word_subword (read YMM3 s26) (224,32)] =
      REJ_SAMPLE(SUB_LIST(8*i,8) inlist)`
    ASSUME_TAC THENL
     [REWRITE_TAC[REJ_SAMPLE] THEN
      REPEAT(FIRST_X_ASSUM(K ALL_TAC o check (fun th ->
        can (find_term ((=) `newlen:num`)) (concl th) ||
        can (find_term ((=) `R9`)) (concl th)))) THEN
      REPEAT(FIRST_X_ASSUM(K ALL_TAC o check (fun th ->
        let c = concl th in
        not(can (find_term ((=) `YMM3`)) c &&
            can (find_term ((=) (mk_var("s26",`:x86state`)))) c) &&
        not(can (find_term ((=) `inlist:(24 word)list`)) c &&
            can (find_term (fun t ->
              try fst(dest_const t) = "num_of_wordlist" with _ -> false)) c &&
            can (find_term ((=) (mk_var("s21",`:x86state`)))) c) &&
        (can (find_term (fun t -> try let s = fst(dest_var t) in
           String.length s > 0 && s.[0] = 's' && s <> "stackpointer"
           with _ -> false)) c ||
         can (find_term ((=) `MAYCHANGE`)) c ||
         can (find_term ((=) `bytes_loaded`)) c)))) THEN
      FIRST_X_ASSUM(fun th ->
        if can (find_term ((=) `YMM3`)) (concl th) &&
           can (find_term ((=) (mk_var("s26",`:x86state`)))) (concl th) &&
           is_eq(concl th)
        then GEN_REWRITE_TAC (ONCE_DEPTH_CONV) [th]
        else failwith "") THEN
      CONV_TAC(TOP_DEPTH_CONV
        (REWR_CONV WORD_SUBWORD_AND ORELSEC WORD_SIMPLE_SUBWORD_CONV)) THEN
      CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV) THEN
      SUBGOAL_THEN `1 * val(word(24 * i):int64) = 24 * i` SUBST1_TAC THENL
       [REWRITE_TAC[MULT_CLAUSES; VAL_WORD; DIMINDEX_64] THEN
        CONV_TAC NUM_REDUCE_CONV THEN MATCH_MP_TAC MOD_LT THEN
        UNDISCH_TAC `24 * i <= 808` THEN ARITH_TAC;
        ALL_TAC] THEN
      REWRITE_TAC[BYTE_JOIN_ZX; BYTE_JOIN_SUBWORD_ZX;
                  bytes256; READ_COMPONENT_COMPOSE; asword; through; read] THEN
      CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV) THEN
      SUBGOAL_THEN
        `read(memory :> bytes(word_add buf (word(24*i)),24)) s21 =
         num_of_wordlist(SUB_LIST(8*i,8) (inlist:(24 word)list))`
      ASSUME_TAC THENL
       [REWRITE_TAC[NUM_OF_WORDLIST_SUB_LIST; DIMINDEX_24] THEN
        CONV_TAC NUM_REDUCE_CONV THEN
        FIRST_ASSUM(fun th ->
          if is_eq(concl th) &&
             can (find_term (fun t ->
               try fst(dest_const t) = "num_of_wordlist" with _ -> false)) (concl th) &&
             not(can (find_term (fun t ->
               try fst(dest_const t) = "SUB_LIST" with _ -> false)) (concl th)) &&
             (let s = string_of_term(concl th) in
              let n = String.length s in
              let rec has840 j = j + 2 < n &&
                (s.[j] = '8' && s.[j+1] = '4' && s.[j+2] = '0' || has840 (j+1)) in
              has840 0)
          then GEN_REWRITE_TAC (RAND_CONV o LAND_CONV o LAND_CONV) [GSYM th]
          else failwith "") THEN
        REWRITE_TAC[GSYM READ_BYTES_DIV; GSYM READ_BYTES_MOD;
                    ARITH_RULE `8 * (24 * i) = 192 * i`;
                    ARITH_RULE `8 * 24 = 192`] THEN
        REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_DIV; READ_BYTES_MOD] THEN
        CONV_TAC NUM_REDUCE_CONV THEN
        SUBGOAL_THEN `MIN (840 - 24 * i) 24 = 24` SUBST1_TAC THENL
         [REWRITE_TAC[MIN] THEN
          UNDISCH_TAC `24 * i <= 808` THEN ARITH_TAC;
          REWRITE_TAC[ARITH_RULE `24 * 8 * i = 8 * (24 * i)`] THEN
          GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV)
            [GSYM(NUM_REDUCE_CONV `2 EXP (8 * 24)`)] THEN
          REWRITE_TAC[READ_BYTES_DIV; READ_BYTES_MOD] THEN
          CONV_TAC NUM_REDUCE_CONV THEN
          SUBGOAL_THEN `MIN (840 - 24 * i) 24 = 24` SUBST1_TAC THENL
           [REWRITE_TAC[MIN] THEN
            UNDISCH_TAC `24 * i <= 808` THEN ARITH_TAC;
            REFL_TAC]];
        ALL_TAC] THEN
      SUBGOAL_THEN
        `read(bytes(word_add buf (word(24*i)),32))(read memory s21) MOD
         2 EXP 192 =
         num_of_wordlist(SUB_LIST(8*i,8) (inlist:(24 word)list))`
      MP_TAC THENL
       [FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[READ_COMPONENT_COMPOSE]) THEN
        DISCH_THEN(SUBST1_TAC o SYM) THEN
        GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV)
          [GSYM(NUM_REDUCE_CONV `8 * 24`)] THEN
        REWRITE_TAC[READ_BYTES_MOD] THEN CONV_TAC NUM_REDUCE_CONV THEN
        REWRITE_TAC[MIN; ARITH_RULE `24 <= 32`];
        ALL_TAC] THEN
      ABBREV_TAC
        `n32 = read(bytes(word_add buf (word(24*i)),32))(read memory s21)` THEN
      DISCH_TAC THEN
      ASM_REWRITE_TAC[VAL_MOD_23_EQ_AND; COEFF_FROM_BYTES;
                      EL_NUM_OF_WORDLIST; NUM_OF_WORDLIST_SUB_LIST;
                      DIMINDEX_24] THEN
      CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV) THEN
      ASM_REWRITE_TAC[] THEN
      (* COEFF_BYTE_JOIN_WORD converts byte_join coefficients to word(n MOD 2^256 DIV 2^ofs MOD 2^23).
         Use GEN_REWRITE with concrete instances for each of the 8 offsets. *)
      (* Combined COEFF + MOD_256_192: byte_join coeffs → word(n32 MOD 2^192 DIV 2^k MOD 2^23) *)
      GEN_REWRITE_TAC (LAND_CONV o DEPTH_CONV)
        (map (fun k ->
          let kterm = mk_small_numeral k in
          let coeff_th = CONV_RULE NUM_REDUCE_CONV
            (SPECL [`n32:num`; kterm] COEFF_BYTE_JOIN_WORD) in
          let mod_th = CONV_RULE NUM_REDUCE_CONV
            (SPECL [`n32:num`; kterm] MOD_256_192) in
          CONV_RULE NUM_REDUCE_CONV (TRANS coeff_th (AP_TERM `word:num->int32` mod_th)))
        [0;24;48;72;96;120;144;168]) THEN
      CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[DIV_1] THEN
      (* Convert huge 2^192 numeral back to 2 EXP 192 so hypothesis can match *)
      REWRITE_TAC[GSYM(NUM_REDUCE_CONV `2 EXP 192`)] THEN
      ASM_REWRITE_TAC[] THEN
      (* Prove LENGTH(SUB_LIST(8*i,8) inlist) = 8 for REJ_SAMPLE_COEFFS *)
      SUBGOAL_THEN `LENGTH(SUB_LIST(8*i,8) (inlist:(24 word)list)) = 8`
        ASSUME_TAC THENL
       [REWRITE_TAC[LENGTH_SUB_LIST] THEN
        CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN
        MATCH_MP_TAC(ARITH_RULE
          `8 * i + 8 <= l ==> MIN 8 (l - 8 * i) = 8`) THEN
        ASM_ARITH_TAC;
        ALL_TAC] THEN
      ASM_SIMP_TAC[CONV_RULE NUM_REDUCE_CONV MAP_REJ_COEFFS];
      ALL_TAC] THEN

    (* Derive LENGTH from FILTER equality for the ABBREV *)
    FIRST_X_ASSUM(fun th ->
      if can (find_term (fun t -> try fst(dest_const t) = "FILTER" with _ -> false)) (concl th) &&
         can (find_term (fun t -> try fst(dest_const t) = "REJ_SAMPLE" with _ -> false)) (concl th) &&
         is_eq(concl th) &&
         not(can (find_term ((=) `LENGTH:(int32 list)->num`)) (concl th))
      then ASSUME_TAC th THEN ASSUME_TAC(AP_TERM `LENGTH:(int32 list)->num` th)
      else failwith "not filter_eq") THEN

    (* Abbreviate the FILTER length to prevent DISCARD from seeing s26 ref *)
    ABBREV_TAC `newlen = LENGTH(FILTER (\c:int32. val c < 8380417)
        [word_subword (read YMM3 s26:int256) (0,32):int32;
         word_subword (read YMM3 s26) (32,32);
         word_subword (read YMM3 s26) (64,32);
         word_subword (read YMM3 s26) (96,32);
         word_subword (read YMM3 s26) (128,32);
         word_subword (read YMM3 s26) (160,32);
         word_subword (read YMM3 s26) (192,32);
         word_subword (read YMM3 s26) (224,32)])` THEN

    (* The hypothesis `newlen = LENGTH(REJ_SAMPLE(SUB_LIST(8*i,8) inlist))`
       already exists from the SIMD subgoal proof. It's state-free and
       survives DISCARD. No need to re-derive it. *)

    (* Derive FILTER = REJ_SAMPLE BEFORE ABBREVs, while all state hyps exist.
       The SIMD subgoal proved LENGTH equality. Now prove FILTER equality
       by using read YMM3 s26 = read YMM3 s29 (unchanged through s27-s29). *)
    SUBGOAL_THEN
      `FILTER (\c:int32. val c < 8380417)
         [word_subword (read YMM3 s29:int256) (0,32):int32;
          word_subword (read YMM3 s29) (32,32);
          word_subword (read YMM3 s29) (64,32);
          word_subword (read YMM3 s29) (96,32);
          word_subword (read YMM3 s29) (128,32);
          word_subword (read YMM3 s29) (160,32);
          word_subword (read YMM3 s29) (192,32);
          word_subword (read YMM3 s29) (224,32)] =
       REJ_SAMPLE(SUB_LIST(8*i,8) (inlist:(24 word)list))`
    ASSUME_TAC THENL
     [(* Use the FILTER=REJ_SAMPLE hypothesis (s26 version) to reduce to
        FILTER P [s29 lanes] = FILTER P [s26 lanes], then ASM_REWRITE closes
        because read YMM3 s29 = read YMM3 s26 (same VPAND EXPR). *)
      FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
        can (find_term (fun t -> try fst(dest_const t) = "FILTER" with _ -> false)) (concl th) &&
        can (find_term (fun t -> try fst(dest_const t) = "REJ_SAMPLE" with _ -> false)) (concl th) &&
        is_eq(concl th) &&
        not(can (find_term ((=) `LENGTH:(int32 list)->num`)) (concl th)))) THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN

    (* Save the 8 bounds val(word_subword (read YMM3 s29) (k,32)) < 8388608
       BEFORE ABBREV substitutes coeffs_ymm3. Otherwise these bounds are
       consumed as intermediate lemmas during CMP_MASK discharge and the
       later VPERMD block's Step F picker (which looks for
       `word_subword coeffs_ymm3 (k,32) ... < 8388608`) fails with Not_found. *)
    SUBGOAL_THEN
     `val(word_subword (read YMM3 s29:int256) (0,32):int32) < 8388608 /\
      val(word_subword (read YMM3 s29:int256) (32,32):int32) < 8388608 /\
      val(word_subword (read YMM3 s29:int256) (64,32):int32) < 8388608 /\
      val(word_subword (read YMM3 s29:int256) (96,32):int32) < 8388608 /\
      val(word_subword (read YMM3 s29:int256) (128,32):int32) < 8388608 /\
      val(word_subword (read YMM3 s29:int256) (160,32):int32) < 8388608 /\
      val(word_subword (read YMM3 s29:int256) (192,32):int32) < 8388608 /\
      val(word_subword (read YMM3 s29:int256) (224,32):int32) < 8388608`
     STRIP_ASSUME_TAC THENL
      [FIRST_ASSUM(fun th ->
         let c = concl th in
         if is_eq c &&
            (try fst(dest_const(fst(strip_comb(rhs c)))) = "word_and" with _ -> false) &&
            (try let l = lhs c in
                 fst(dest_const(rator l)) = "read" &&
                 fst(dest_const(rand(rator l))) = "YMM3"
             with _ -> false)
         then SUBST1_TAC th
         else failwith "no YMM3 word_and") THEN
       REWRITE_TAC[WORD_SUBWORD_AND] THEN
       CONV_TAC(DEPTH_CONV(WORD_SIMPLE_SUBWORD_CONV ORELSEC WORD_NUM_RED_CONV)) THEN
       REPEAT CONJ_TAC THEN
       MATCH_MP_TAC(ARITH_RULE `n <= 8388607 ==> n < 8388608`) THEN
       REWRITE_TAC[VAL_WORD_AND_WORD_LE];
       ALL_TAC] THEN

    (* Ghost state: ABBREV key s29 values before DISCARD kills them. *)
    ABBREV_TAC `coeffs_ymm3:int256 = read YMM3 s29` THEN
    ABBREV_TAC `cmp_mask:int64 = read R8 s29` THEN
    ABBREV_TAC `table_entry:int64 =
      read (memory :> bytes64 (word_add table (word (8 * val (cmp_mask:int64))))) s29` THEN

    (* Preserve cmp_mask ↔ coefficient comparison relationship.
       cmp_mask encodes which coefficients pass val < Q via VMOVMSKPS.
       This connects cmp_mask to the FILTER predicate for the brute force. *)
    SUBGOAL_THEN
      `val(cmp_mask:int64) =
       bitval(val(word_subword (coeffs_ymm3:int256) (0,32):int32) < 8380417) +
       2 * bitval(val(word_subword (coeffs_ymm3:int256) (32,32):int32) < 8380417) +
       4 * bitval(val(word_subword (coeffs_ymm3:int256) (64,32):int32) < 8380417) +
       8 * bitval(val(word_subword (coeffs_ymm3:int256) (96,32):int32) < 8380417) +
       16 * bitval(val(word_subword (coeffs_ymm3:int256) (128,32):int32) < 8380417) +
       32 * bitval(val(word_subword (coeffs_ymm3:int256) (160,32):int32) < 8380417) +
       64 * bitval(val(word_subword (coeffs_ymm3:int256) (192,32):int32) < 8380417) +
       128 * bitval(val(word_subword (coeffs_ymm3:int256) (224,32):int32) < 8380417)`
      ASSUME_TAC THENL
     [(* Use CMP_MASK_CORRECT: rewrite H31 (cmp_mask ABBREV) using GSYM H30
        (coeffs_ymm3 ABBREV) to replace the VPAND chain with coeffs_ymm3,
        then apply the lemma directly. *)
      FIRST_ASSUM(fun h30 ->
        if is_eq(concl h30) && is_var(lhs(concl h30)) &&
           (try fst(dest_var(lhs(concl h30))) = "coeffs_ymm3" with _ -> false) &&
           (try fst(dest_const(fst(strip_comb(rhs(concl h30))))) = "word_and"
            with _ -> false)
        then
          FIRST_ASSUM(fun h31 ->
            if is_eq(concl h31) && is_var(lhs(concl h31)) &&
               (try fst(dest_var(lhs(concl h31))) = "cmp_mask" with _ -> false) &&
               (try fst(dest_const(fst(strip_comb(rhs(concl h31))))) = "word_zx"
                with _ -> false)
            then
              SUBST1_TAC(REWRITE_RULE[GSYM h30] h31)
            else failwith "not h31")
        else failwith "not h30") THEN
      (* Normalize the bit-31/word_subword/word-of-sum shape to match
         CMP_MASK_CORRECT's word_of_bits form: first collapse the
         bit 31 (word_subword x (k,32)) patterns via GSYM BIT_SUBWORD_256
         (so we see bit (32k+31) of the nested word_join), then fold the
         word(sum of bitvals) via GSYM VMOVMSKPS_BYTE_EQ into word_of_bits. *)
      REWRITE_TAC[GSYM BIT_SUBWORD_256; GSYM VMOVMSKPS_BYTE_EQ] THEN
      MATCH_MP_TAC(ISPECL [
        `word_subword (coeffs_ymm3:int256) (0,32):int32`;
        `word_subword (coeffs_ymm3:int256) (32,32):int32`;
        `word_subword (coeffs_ymm3:int256) (64,32):int32`;
        `word_subword (coeffs_ymm3:int256) (96,32):int32`;
        `word_subword (coeffs_ymm3:int256) (128,32):int32`;
        `word_subword (coeffs_ymm3:int256) (160,32):int32`;
        `word_subword (coeffs_ymm3:int256) (192,32):int32`;
        `word_subword (coeffs_ymm3:int256) (224,32):int32`
      ] CMP_MASK_CORRECT) THEN
      (* Prove val(word_subword coeffs_ymm3 (k,32)) < 8388608 for each k.
         coeffs_ymm3 = word_and(big)(mask) so word_subword distributes,
         mask subword = word 8388607, then VAL_WORD_AND_WORD_LE gives bound. *)
      FIRST_ASSUM(fun h30 ->
        if is_eq(concl h30) && is_var(lhs(concl h30)) &&
           (try fst(dest_var(lhs(concl h30))) = "coeffs_ymm3" with _ -> false) &&
           (try fst(dest_const(fst(strip_comb(rhs(concl h30))))) = "word_and"
            with _ -> false)
        then SUBST1_TAC h30
        else failwith "") THEN
      REWRITE_TAC[WORD_SUBWORD_AND] THEN
      CONV_TAC(DEPTH_CONV(WORD_SIMPLE_SUBWORD_CONV ORELSEC WORD_NUM_RED_CONV)) THEN
      REPEAT CONJ_TAC THEN
      MATCH_MP_TAC(ARITH_RULE `n <= 8388607 ==> n < 8388608`) THEN
      REWRITE_TAC[VAL_WORD_AND_WORD_LE];
      ALL_TAC] THEN

    DISCARD_OLDSTATE_TAC "s29" THEN CLARIFY_TAC THEN
    (* Step 30-32 WITHOUT discard to keep VPERMD hypothesis chain *)
    X86_VSTEPS_TAC MLDSA_REJ_UNIFORM_EXEC (30--32) THEN
    SUBGOAL_THEN
      `val(read YMM3 s32:int256) MOD 2 EXP (32 * newlen) =
       num_of_wordlist(REJ_SAMPLE(SUB_LIST(8*i,8) (inlist:(24 word)list)))`
      ASSUME_TAC THENL
     [(* VPERMD: apply MLDSA_VPERMD_BRIDGE (proven in defs_extra.ml)
         — replaces the former 256-case brute force, eliminating 255 cheats. *)
      (* Step A: derive val(table_entry) = (table DIV 2^(64*val cmp_mask)) MOD 2^64 *)
      SUBGOAL_THEN
        `val(table_entry:int64) =
         (num_of_wordlist mldsa_rej_uniform_table DIV
          2 EXP (64 * val(cmp_mask:int64))) MOD 2 EXP 64`
        ASSUME_TAC THENL
       [SUBGOAL_THEN
          `val(read(memory :> bytes64(word_add table (word(8 * val(cmp_mask:int64))))) s32 :int64) =
           (num_of_wordlist mldsa_rej_uniform_table DIV 2 EXP (64 * val cmp_mask)) MOD 2 EXP 64`
          MP_TAC THENL
         [MATCH_MP_TAC TABLE_ENTRY_FROM_MEMORY THEN CONJ_TAC THENL
           [ASM_REWRITE_TAC[];
            FIRST_X_ASSUM(fun th ->
              if can (find_term ((=) `bitval`)) (concl th) && is_eq(concl th) &&
                 (try fst(dest_var(rand(lhs(concl th)))) = "cmp_mask" with _ -> false)
              then SUBST1_TAC th else failwith "") THEN
            MP_TAC(SPEC `val(word_subword (coeffs_ymm3:int256) (0,32):int32) < 8380417` BITVAL_BOUND) THEN
            MP_TAC(SPEC `val(word_subword (coeffs_ymm3:int256) (32,32):int32) < 8380417` BITVAL_BOUND) THEN
            MP_TAC(SPEC `val(word_subword (coeffs_ymm3:int256) (64,32):int32) < 8380417` BITVAL_BOUND) THEN
            MP_TAC(SPEC `val(word_subword (coeffs_ymm3:int256) (96,32):int32) < 8380417` BITVAL_BOUND) THEN
            MP_TAC(SPEC `val(word_subword (coeffs_ymm3:int256) (128,32):int32) < 8380417` BITVAL_BOUND) THEN
            MP_TAC(SPEC `val(word_subword (coeffs_ymm3:int256) (160,32):int32) < 8380417` BITVAL_BOUND) THEN
            MP_TAC(SPEC `val(word_subword (coeffs_ymm3:int256) (192,32):int32) < 8380417` BITVAL_BOUND) THEN
            MP_TAC(SPEC `val(word_subword (coeffs_ymm3:int256) (224,32):int32) < 8380417` BITVAL_BOUND) THEN
            ARITH_TAC];
          ASM_REWRITE_TAC[]]; ALL_TAC] THEN
      (* Step B: substitute read YMM3 s32 into goal (exposes the VPERMD expansion). *)
      FIRST_X_ASSUM (fun th ->
        let s = string_of_term (concl th) in
        let n = String.length s in
        let contains needle =
          let k = String.length needle in
          let rec scan i = i + k <= n && (String.sub s i k = needle || scan (i+1)) in
          scan 0 in
        if contains "read YMM3 s32" && is_eq(concl th) && not(contains "MAYCHANGE")
        then GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [th] THEN ASSUME_TAC th
        else failwith "not ymm3 s32") THEN
      (* Step C: rewrite (32 * newlen) → (32 * bitval_sum) via newlen = LENGTH(FILTER)
         and FILTER=REJ_SAMPLE; also convert RHS REJ_SAMPLE → FILTER. *)
      (fun (asl, w) ->
        let contains_s needle s =
          let n = String.length needle in let m = String.length s in
          let rec scan i = i + n <= m && (String.sub s i n = needle || scan (i+1)) in
          scan 0 in
        let b k =
          let needle = Printf.sprintf "word_subword coeffs_ymm3 (%d,32)" k in
          snd(List.find (fun (_,th) ->
            let s = string_of_term (concl th) in
            contains_s needle s && contains_s "< 8388608" s && not(contains_s "==>" s)) asl) in
        let bounds = CONJ (b 0) (CONJ (b 32) (CONJ (b 64) (CONJ (b 96) (CONJ (b 128) (CONJ (b 160) (CONJ (b 192) (b 224))))))) in
        let flt_spec = ISPECL [
          `word_subword (coeffs_ymm3:int256) (0,32):int32`;
          `word_subword (coeffs_ymm3:int256) (32,32):int32`;
          `word_subword (coeffs_ymm3:int256) (64,32):int32`;
          `word_subword (coeffs_ymm3:int256) (96,32):int32`;
          `word_subword (coeffs_ymm3:int256) (128,32):int32`;
          `word_subword (coeffs_ymm3:int256) (160,32):int32`;
          `word_subword (coeffs_ymm3:int256) (192,32):int32`;
          `word_subword (coeffs_ymm3:int256) (224,32):int32`
        ] FILTER_LENGTH_8 in
        let length_filter_eq = MP flt_spec bounds in
        let newlen_def = snd(List.find (fun (_, th) ->
          is_eq(concl th) && is_var(lhs(concl th)) &&
          (try fst(dest_var(lhs(concl th))) = "newlen" with _ -> false)) asl) in
        let filter_rej_eq = snd(List.find (fun (_, th) ->
          let s = string_of_term (concl th) in
          contains_s "FILTER" s && contains_s "REJ_SAMPLE" s && is_eq(concl th) &&
          not(contains_s "LENGTH" s) && not(contains_s "==>" s)) asl) in
        let newlen_bitval = TRANS (TRANS newlen_def
          (AP_TERM `LENGTH:int32 list -> num` (SYM filter_rej_eq))) length_filter_eq in
        REWRITE_TAC[newlen_bitval; SYM filter_rej_eq] (asl, w)) THEN
      (* Step D: fold raw memory read back to table_entry, then collapse word_zx(word_zx ...) via
         WORD_SIMPLE_SUBWORD_CONV to expose word_subword table_entry (k,3). *)
      (fun (asl, w) ->
        let contains_s needle s =
          let n = String.length needle in let m = String.length s in
          let rec scan i = i + n <= m && (String.sub s i n = needle || scan (i+1)) in
          scan 0 in
        let cm_sym =
          let th = snd(List.find (fun (_, th) ->
            is_eq(concl th) &&
            (try fst(dest_var(rand(lhs(concl th)))) = "cmp_mask" with _ -> false) &&
            contains_s "bitval" (string_of_term (concl th))) asl) in
          SYM th in
        let te_eqs = List.filter_map (fun (_, th) ->
          let s = string_of_term (concl th) in
          if is_eq(concl th) && contains_s "table_entry" s && contains_s "bytes64" s
          then Some th else None) asl in
        (REWRITE_TAC[cm_sym] THEN REWRITE_TAC te_eqs THEN
         CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV)) (asl, w)) THEN
      (* Step E: apply MLDSA_VPERMD_BRIDGE specialized to coeffs_ymm3 and table_entry. *)
      MATCH_MP_TAC (ISPECL [`coeffs_ymm3:int256`; `table_entry:int64`] MLDSA_VPERMD_BRIDGE) THEN
      (* Step F: discharge the antecedent using targeted rewrites (bounds + te_val + cm_sym).
         Full ASM_REWRITE_TAC hangs on the large assumption list, but this focused
         set closes the 9 antecedent conjuncts in ~2s. *)
      W(fun (asl,_) ->
        let contains_s needle s =
          let n = String.length needle in let m = String.length s in
          let rec scan i = i + n <= m && (String.sub s i n = needle || scan (i+1)) in
          scan 0 in
        let b k =
          let needle = Printf.sprintf "word_subword coeffs_ymm3 (%d,32)" k in
          snd(List.find (fun (_,th) ->
            let s = string_of_term (concl th) in
            contains_s needle s && contains_s "< 8388608" s && not(contains_s "==>" s)) asl) in
        let cm_sym =
          let th = snd(List.find (fun (_, th) ->
            is_eq(concl th) &&
            (try fst(dest_var(rand(lhs(concl th)))) = "cmp_mask" with _ -> false) &&
            contains_s "bitval" (string_of_term (concl th))) asl) in
          SYM th in
        let te_val = snd(List.find (fun (_, th) ->
          is_eq(concl th) &&
          (try let l = lhs(concl th) in
               fst(dest_comb l) = `val:int64->num` &&
               fst(dest_var(rand l)) = "table_entry"
           with _ -> false) &&
          contains_s "DIV" (string_of_term (concl th))) asl) in
        REWRITE_TAC [b 0; b 32; b 64; b 96; b 128; b 160; b 192; b 224; te_val; cm_sym]);
      ALL_TAC] THEN
    (* VSTEPS for all 3 steps to preserve bytes256 + VPERMD hyps *)
    (fun gl -> Printf.printf "  LOOP[7c]: steps 33-35 (VSTEPS)\n%!"; ALL_TAC gl) THEN
    X86_VSTEPS_TAC MLDSA_REJ_UNIFORM_EXEC (33--35) THEN
    (fun gl -> Printf.printf "  LOOP[8]: steps done\n%!"; ALL_TAC gl) THEN

    (* (e) COND_CASES_TAC: continue (i+1 < N) vs exit (~(i+1 < N)) *)
    (fun gl -> Printf.printf "  DEBUG[A]: before COND_CASES_TAC\n%!"; ALL_TAC gl) THEN
    COND_CASES_TAC THENL
     [(* i+1 < N: continue looping *)
      (fun gl -> Printf.printf "  DEBUG[B]: continue branch\n%!"; ALL_TAC gl) THEN
      (* Derive new region memory content BEFORE ENSURES consumes state.
         From the bytes256 write hypothesis (VMOVDQU step), derive:
           read(memory :> bytes(addr, 32)) sN = val(bytes256 RHS)
         with address normalized (val(word curlen) → curlen).
         This is used by VPERMD_MEMORY_BRIDGE in the memory store goal. *)
      (fun (asl,w) ->
        try
          (* Find bytes256 hyp with s35 and res in address *)
          let b256_th = snd(find (fun (_,th) ->
            is_eq(concl th) &&
            can (find_term (fun t -> try fst(dest_const t) = "bytes256" with _ -> false)) (concl th) &&
            can (find_term (fun t -> try fst(dest_var t) = "res" with _ -> false)) (concl th) &&
            can (find_term (fun t -> try fst(dest_var t) = "s35" with _ -> false)) (concl th) &&
            not(can (find_term (fun t -> try fst(dest_const t) = "MAYCHANGE" with _ -> false)) (concl th))) asl) in
          (* Find read YMM3 s35 = <expr> to get clean RHS *)
          let has_const name t = try fst(dest_const t) = name with _ -> false in
          let has_var name t = try fst(dest_var t) = name with _ -> false in
          let ymm3_s35 = snd(find (fun (_,th) ->
            is_eq(concl th) &&
            can (find_term (has_var "s35")) (lhs(concl th)) &&
            can (find_term (has_const "YMM3")) (lhs(concl th)) &&
            not(can (find_term (has_const "MOD")) (concl th)) &&
            not(can (find_term (has_const "bytes256")) (concl th))) asl) in
          (* Chain: bytes256 s35 = <expr> = YMM3 s35 by transitivity *)
          let b256_ymm3 = TRANS b256_th (SYM ymm3_s35) in
          (* Normalize address: val(word curlen) → curlen *)
          let curlen_bound = snd(find (fun (_,th) ->
            try concl th = `curlen <= 248` with _ -> false) asl) in
          let mk_norm dim_thm dim_val =
            let vwe = CONV_RULE NUM_REDUCE_CONV (REWRITE_RULE[dim_thm] (INST_TYPE [dim_val,`:N`] VAL_WORD_EQ)) in
            let lt = CONV_RULE NUM_REDUCE_CONV
              (MATCH_MP (ARITH_RULE `n <= 248 ==> n < 4294967296`) curlen_bound) in
            try MATCH_MP vwe lt with _ ->
              let lt64 = CONV_RULE NUM_REDUCE_CONV
                (MATCH_MP (ARITH_RULE `n <= 248 ==> n < 18446744073709551616`) curlen_bound) in
              MATCH_MP vwe lt64 in
          let curlen_norm_32 = mk_norm DIMINDEX_32 `:32` in
          let curlen_norm_64 = mk_norm DIMINDEX_64 `:64` in
          let b256_norm = REWRITE_RULE[curlen_norm_32; curlen_norm_64] b256_ymm3 in
          (* Convert: val(bytes256 addr s35) = val(read YMM3 s35) + address normalize *)
          let val_eq = AP_TERM `val:int256->num` b256_norm in
          let bytes32_eq = CONV_RULE(LAND_CONV(
            REWRITE_CONV[READ_COMPONENT_COMPOSE; VAL_READ_BYTES256] THENC
            REWRITE_CONV[GSYM READ_COMPONENT_COMPOSE])) val_eq in
          (* Result: read(memory :> bytes(addr,32)) s35 = val(read YMM3 s35) *)
          ASSUME_TAC bytes32_eq (asl,w)
        with e ->
          Printf.printf "  PRE-ENSURES: derivation failed: %s\n%!" (Printexc.to_string e);
          ALL_TAC (asl,w)) THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
      (fun gl -> Printf.printf "  DEBUG[C]: after ASM_REWRITE, before let_CONV\n%!"; ALL_TAC gl) THEN
      CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
      (fun gl -> Printf.printf "  DEBUG[D]: after let_CONV, before iteration bounds\n%!"; ALL_TAC gl) THEN
      (* Establish iteration bounds *)
      SUBGOAL_THEN `8 * (i + 1) <= LENGTH(inlist:(24 word)list)` ASSUME_TAC THENL
       [ASM_REWRITE_TAC[] THEN
        UNDISCH_TAC `24 * (i + 1) <= 832` THEN ARITH_TAC;
        ALL_TAC] THEN
      (fun gl -> Printf.printf "  DEBUG[E]: before FIRST_X_ASSUM newlen subst\n%!"; ALL_TAC gl) THEN
      (* Use the SIMD↔spec result: newlen = LENGTH(REJ_SAMPLE(SUB_LIST(8*i,8)))
         ABBREV_TAC replaced FILTER... with newlen in this hypothesis *)
      FIRST_X_ASSUM(SUBST1_TAC o check (fun th ->
        is_eq(concl th) &&
        can (find_term ((=) `newlen:num`)) (concl th) &&
        can (find_term (fun t ->
          try fst(dest_const t) = "REJ_SAMPLE" with _ -> false)) (concl th))) THEN
      (fun gl -> Printf.printf "  DEBUG[F]: before SIMD_ITERATION_BRIDGE\n%!"; ALL_TAC gl) THEN
      (* Apply SIMD_ITERATION_BRIDGE to split REJ_SAMPLE across iterations *)
      MP_TAC(ISPECL [`inlist:(24 word)list`; `i:num`; `curlist:int32 list`; `curlen:num`]
        SIMD_ITERATION_BRIDGE) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
      (fun gl -> Printf.printf "  DEBUG[G]: before LENGTH_APPEND rewrite\n%!"; ALL_TAC gl) THEN
      ASM_REWRITE_TAC[LENGTH_APPEND; NUM_OF_WORDLIST_APPEND] THEN
      (fun gl -> Printf.printf "  DEBUG[H]: before DISCARD state\n%!"; ALL_TAC gl) THEN
      (* Clean state hypotheses before word arithmetic — keep MAYCHANGE and memory *)
      DISCARD_ASSUMPTIONS_TAC (fun th ->
        let c = concl th in
        (can (term_match [] `read x s = (y:num)`) c &&
         not (can (find_term (fun t -> try fst(dest_const t) = "memory" with _ -> false)) c)) ||
        can (term_match [] `bytes_loaded x y z`) c ||
        can (term_match [] `read x s <=> y`) c) THEN
      ABBREV_TAC `lenrej = LENGTH(REJ_SAMPLE(SUB_LIST(8*i,8) inlist))` THEN
      (fun gl -> Printf.printf "  DEBUG[I]: before REPEAT CONJ_TAC (data goals)\n%!"; ALL_TAC gl) THEN
      REPEAT CONJ_TAC THENL
       [(* RAX: word(curlen + lenrej) — word arithmetic.
           Use targeted UNDISCH (not ASM_ARITH_TAC — hangs on ~200 asl). *)
        REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_ZX_GEN; VAL_WORD_ADD; VAL_WORD;
                    DIMINDEX_32; DIMINDEX_64] THEN
        CONV_TAC NUM_REDUCE_CONV THEN
        UNDISCH_TAC `curlen <= 248` THEN UNDISCH_TAC `lenrej <= 8` THEN
        SPEC_TAC(`lenrej:num`, `l:num`) THEN GEN_TAC THEN
        SPEC_TAC(`curlen:num`, `c:num`) THEN GEN_TAC THEN
        REPEAT DISCH_TAC THEN
        SUBGOAL_THEN `c < 4294967296 /\ c < 18446744073709551616 /\
                      l < 4294967296 /\ l < 18446744073709551616 /\
                      c + l < 4294967296 /\ c + l < 18446744073709551616`
          STRIP_ASSUME_TAC THENL
         [UNDISCH_TAC `c <= 248` THEN UNDISCH_TAC `l <= 8` THEN ARITH_TAC;
          ALL_TAC] THEN
        ASM_SIMP_TAC[MOD_LT] THEN ARITH_TAC;
        (* RCX: word(24*(i+1)) — word arithmetic *)
        REWRITE_TAC[ARITH_RULE `24 * (i + 1) = 24 * i + 24`] THEN
        REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_ZX_GEN; VAL_WORD_ADD; VAL_WORD;
                    DIMINDEX_32; DIMINDEX_64] THEN
        CONV_TAC NUM_REDUCE_CONV THEN
        UNDISCH_TAC `24 * i <= 808` THEN
        SPEC_TAC(`24 * i`, `n:num`) THEN GEN_TAC THEN DISCH_TAC THEN
        SUBGOAL_THEN `n < 4294967296 /\ n < 18446744073709551616 /\
                      n + 24 < 4294967296 /\ n + 24 < 18446744073709551616`
          STRIP_ASSUME_TAC THENL
         [UNDISCH_TAC `n <= 808` THEN ARITH_TAC; ALL_TAC] THEN
        ASM_SIMP_TAC[MOD_LT] THEN ARITH_TAC;
        (* Memory store: use VPERMD_MEMORY_BRIDGE
           We have (from PRE-ENSURES):
             read(memory :> bytes(addr, 32)) s35 = val(read YMM3 sN)
           And (from VPERMD):
             val(read YMM3 sN) MOD 2^(32*lenrej) = num_of_wordlist(REJ_SAMPLE(...))
           VPERMD_MEMORY_BRIDGE chains these to close the sub-read goal. *)
        (fun gl -> Printf.printf "  MEMSTORE: VPERMD_MEMORY_BRIDGE\n%!"; ALL_TAC gl) THEN
        REWRITE_TAC[DIMINDEX_32;
                    ARITH_RULE `4 * (curlen + lenrej) = 4 * curlen + 4 * lenrej`;
                    ARITH_RULE `32 * curlen = 8 * (4 * curlen)`] THEN
        REWRITE_TAC[MEMORY_BYTES_SPLIT] THEN
        ASM_REWRITE_TAC[] THEN
        REWRITE_TAC[EQ_ADD_LCANCEL; EQ_MULT_LCANCEL; EXP_EQ_0; ARITH_EQ] THEN
        (* Goal: read(bytes(addr, 4*lenrej)) s35 = num_of_wordlist(REJ_SAMPLE(...))
           Use VPERMD_MEMORY_BRIDGE with the PRE-ENSURES bytes32 hypothesis.
           First find the hypothesis, then build the full closing tactic. *)
        (fun (asl,w) ->
          (* Find bytes32 hyp, VPERMD MOD hyp, lenrej bound, then forward-chain *)
          try
            (* 1. bytes32 hypothesis: read(bytes(addr,32)) s35 = vr *)
            let has_const name t = try fst(dest_const t) = name with _ -> false in
            let has_var name t = try fst(dest_var t) = name with _ -> false in
            let bytes32_hyp = snd(List.find (fun (_,th) ->
              is_eq(concl th) &&
              can (find_term (fun t -> try dest_numeral t = Num.num_of_int 32 with _ -> false)) (lhs(concl th)) &&
              can (find_term (fun t -> try fst(dest_var t) = "s35" with _ -> false)) (lhs(concl th)) &&
              can (find_term (fun t -> try fst(dest_var t) = "res" with _ -> false)) (lhs(concl th)) &&
              not(can (find_term (fun t -> try fst(dest_const t) = "bytes256" with _ -> false)) (lhs(concl th)))) asl) in
            (* Find newlen = lenrej hypothesis *)
            let newlen_eq = snd(List.find (fun (_,th) ->
              try is_eq(concl th) && has_var "newlen" (lhs(concl th)) &&
                  has_var "lenrej" (rhs(concl th))
              with _ -> false) asl) in
            (* Find VPERMD MOD hyp: val(YMM3 sN) MOD 2^(32*newlen) = num_of_wordlist(...)
               May be for s34 or s33 — find the most recent one *)
            let vpermd_hyp_raw = snd(List.find (fun (_,th) ->
              is_eq(concl th) &&
              can (find_term (has_const "MOD")) (concl th) &&
              can (find_term (has_var "newlen")) (concl th) &&
              can (find_term (has_const "num_of_wordlist")) (concl th)) asl) in
            (* Normalize: replace newlen with lenrej *)
            let vpermd_hyp_1 = REWRITE_RULE[newlen_eq] vpermd_hyp_raw in
            (* The VPERMD hyp may use a different state (s34) than bytes32 (s35).
               Bridge: find read YMM3 s35 = E and read YMM3 s34 = E, chain them. *)
            let vpermd_hyp = try
              (* Find read YMM3 sN = <int256 expr> — require int256 RHS and YMM3 on LHS *)
              let is_ymm3_read th =
                is_eq(concl th) &&
                type_of(rhs(concl th)) = `:int256` &&
                can (find_term (has_const "YMM3")) (lhs(concl th)) in
              let ymm35 = snd(List.find (fun (_,th) ->
                is_ymm3_read th &&
                can (find_term (has_var "s35")) (lhs(concl th))) asl) in
              let ymm34 = snd(List.find (fun (_,th) ->
                is_ymm3_read th &&
                can (find_term (has_var "s34")) (lhs(concl th))) asl) in
              (* read YMM3 s35 = E, read YMM3 s34 = E => read YMM3 s35 = read YMM3 s34 *)
              let ymm_eq = TRANS ymm35 (SYM ymm34) in
              let val_eq = AP_TERM `val:int256->num` ymm_eq in
              (* Rewrite s34 → s35 in the VPERMD hypothesis *)
              REWRITE_RULE[GSYM val_eq] vpermd_hyp_1
            with _ ->
              vpermd_hyp_1 in
            (* 3. lenrej <= 8: directly available *)
            let lenrej_bound = snd(List.find (fun (_,th) ->
              try is_binary "<=" (concl th) &&
                  has_var "lenrej" (lhand(concl th)) &&
                  dest_small_numeral(rand(concl th)) = 8
              with _ -> false) asl) in
            (* Forward chain: MATCH_MP VPERMD_MEMORY_BRIDGE (bytes32 /\ mod /\ bound) *)
            let bridge = MATCH_MP VPERMD_MEMORY_BRIDGE
              (CONJ bytes32_hyp (CONJ vpermd_hyp lenrej_bound)) in
            REWRITE_TAC[bridge] (asl,w)
          with e ->
            Printf.printf "  MEMSTORE: failed (%s)\n%!" (Printexc.to_string e);
            failwith "memstore bridge derivation failed")];

      (* ~(i+1 < N): exit to pc+181.
         Approach: instead of DISJ_CASES on the outer disjunct, first derive
         N = i+1, then ASM_CASES on `248 < curlen + lenrej`:
           * if true: count-exit fires (JAE at s37 to pc+181) — same as old J2
           * if false: offset-exit path — VSTEPS 38-39 do CMP ecx/JA exit
         This avoids the artificial J1/J2 split that required a separate
         offset-exit proof. *)
      (fun gl -> Printf.printf "  DEBUG[J]: exit branch\n%!"; ALL_TAC gl) THEN
      SUBGOAL_THEN `N = i + 1` ASSUME_TAC THENL
       [UNDISCH_TAC `~(i + 1 < N)` THEN UNDISCH_TAC `i:num < N` THEN ARITH_TAC;
        ALL_TAC] THEN
      X86_VSTEPS_TAC MLDSA_REJ_UNIFORM_EXEC (36--37) THEN
      FIRST_X_ASSUM(DISJ_CASES_TAC o check (is_disj o concl)) THENL
       [(* J1: offset exit (832 < 24 * (N + 1) disjunct holds).
           Split on whether count-exit ALSO fires:
             * J1-A: 248 < curlen + lr  → JAE at s37 fires directly, same as J2.
             * J1-B: curlen + lr <= 248 → JAE falls through, CMP ecx/JA at s38-39
                     fires because 808 < 24*(i+1) (from disjunct + N=i+1). *)
        ASM_CASES_TAC
          `248 < curlen + LENGTH(REJ_SAMPLE(SUB_LIST(8*i,8) (inlist:(24 word)list)))`
        THENL
         [(* J1-A: JAE at s37 fires. Derive J2's precondition, run J2 body. *)
          SUBGOAL_THEN
            `248 < LENGTH(REJ_SAMPLE(SUB_LIST(0,8 * N) (inlist:(24 word)list)))`
            ASSUME_TAC THENL
           [MP_TAC(ISPECL [`inlist:(24 word)list`; `i:num`; `curlist:int32 list`;
                            `curlen:num`] SIMD_ITERATION_BRIDGE) THEN
            ANTS_TAC THENL
             [ASM_REWRITE_TAC[] THEN
              UNDISCH_TAC `24 * (i + 1) <= 832` THEN ARITH_TAC;
              ALL_TAC] THEN
            STRIP_TAC THEN
            ASM_REWRITE_TAC[ARITH_RULE `8 * (i + 1) = 8 * i + 8`;
                            SUB_LIST_SPLIT; REJ_SAMPLE_APPEND; LENGTH_APPEND;
                            ADD_CLAUSES];
            ALL_TAC] THEN
          (* J1-A body is identical to J2 body; run through it.
             Must keep this in sync if J2 body changes. *)
          SUBGOAL_THEN `newlen <= 8` ASSUME_TAC THENL
           [MP_TAC(ISPECL [`inlist:(24 word)list`; `i:num`; `curlist:int32 list`;
                           `curlen:num`] SIMD_ITERATION_BRIDGE) THEN
            ANTS_TAC THENL
             [ASM_REWRITE_TAC[] THEN
              UNDISCH_TAC `24 * (i + 1) <= 832` THEN ARITH_TAC;
              ALL_TAC] THEN
            STRIP_TAC THEN ASM_REWRITE_TAC[];
            ALL_TAC] THEN
          (fun (asl,w) ->
            try
              let has_const name t = try fst(dest_const t) = name with _ -> false in
              let has_var name t = try fst(dest_var t) = name with _ -> false in
              let b256_th = snd(find (fun (_,th) ->
                is_eq(concl th) &&
                can (find_term (has_const "bytes256")) (lhs(concl th)) &&
                not(can (find_term (has_const "MAYCHANGE")) (concl th))) asl) in
              let b256_state = find_term (fun t ->
                try let n = fst(dest_var t) in
                    String.length n > 1 && n.[0] = 's' && type_of t = `:x86state`
                with _ -> false) (lhs(concl b256_th)) in
              let b256_state_name = fst(dest_var b256_state) in
              let ymm_th = snd(find (fun (_,th) ->
                is_eq(concl th) && type_of(rhs(concl th)) = `:int256` &&
                can (find_term (has_const "YMM3")) (lhs(concl th)) &&
                can (find_term (has_var b256_state_name)) (lhs(concl th))) asl) in
              let b256_ymm3 = TRANS b256_th (SYM ymm_th) in
              let curlen_bound = snd(find (fun (_,th) ->
                try concl th = `curlen <= 248` with _ -> false) asl) in
              let vwe32 = CONV_RULE NUM_REDUCE_CONV
                (REWRITE_RULE[DIMINDEX_32] (INST_TYPE [`:32`,`:N`] VAL_WORD_EQ)) in
              let vwe64 = CONV_RULE NUM_REDUCE_CONV
                (REWRITE_RULE[DIMINDEX_64] (INST_TYPE [`:64`,`:N`] VAL_WORD_EQ)) in
              let cn32 = MATCH_MP vwe32 (CONV_RULE NUM_REDUCE_CONV
                (MATCH_MP (ARITH_RULE `n <= 248 ==> n < 4294967296`)
                  curlen_bound)) in
              let cn64 = MATCH_MP vwe64 (CONV_RULE NUM_REDUCE_CONV
                (MATCH_MP (ARITH_RULE `n <= 248 ==> n < 18446744073709551616`)
                  curlen_bound)) in
              let b256_norm = REWRITE_RULE[cn32; cn64] b256_ymm3 in
              let val_eq = AP_TERM `val:int256->num` b256_norm in
              let bytes32_eq = CONV_RULE(LAND_CONV(
                REWRITE_CONV[READ_COMPONENT_COMPOSE; VAL_READ_BYTES256] THENC
                REWRITE_CONV[GSYM READ_COMPONENT_COMPOSE])) val_eq in
              let vpermd_raw = snd(List.find (fun (_,th) ->
                is_eq(concl th) &&
                can (find_term (has_const "MOD")) (concl th) &&
                can (find_term (has_const "num_of_wordlist")) (concl th) &&
                can (find_term (has_var "newlen")) (concl th)) asl) in
              let is_ymm3_read th =
                is_eq(concl th) && type_of(rhs(concl th)) = `:int256` &&
                can (find_term (has_const "YMM3")) (lhs(concl th)) in
              let vpermd_states = List.filter (fun v ->
                let n = fst(dest_var v) in String.length n > 1 && n.[0] = 's' &&
                type_of v = `:x86state`) (frees(concl vpermd_raw)) in
              let vp_state_name = fst(dest_var(List.hd vpermd_states)) in
              let vpermd = try
                let ymm_b32 = snd(List.find (fun (_,th) ->
                  is_ymm3_read th &&
                  can (find_term (has_var b256_state_name))
                    (lhs(concl th))) asl) in
                let ymm_vp = snd(List.find (fun (_,th) ->
                  is_ymm3_read th &&
                  can (find_term (has_var vp_state_name))
                    (lhs(concl th))) asl) in
                let ymm_eq = TRANS ymm_b32 (SYM ymm_vp) in
                let val_eq = AP_TERM `val:int256->num` ymm_eq in
                REWRITE_RULE[GSYM val_eq] vpermd_raw
              with _ -> vpermd_raw in
              let newlen_bound = snd(List.find (fun (_,th) ->
                try is_binary "<=" (concl th) &&
                    (has_var "newlen" (lhand(concl th))) &&
                    dest_small_numeral(rand(concl th)) = 8
                with _ -> false) asl) in
              let bridge = MATCH_MP VPERMD_MEMORY_BRIDGE
                (CONJ bytes32_eq (CONJ vpermd newlen_bound)) in
              ASSUME_TAC bridge (asl,w)
            with _ -> failwith "J1-A PRE-ENSURES") THEN
          ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
          CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN ASM_REWRITE_TAC[] THEN
          SUBGOAL_THEN `N = i + 1` (fun th ->
            REWRITE_TAC[th; ARITH_RULE `8 * (i + 1) = 8 * i + 8`;
                           ARITH_RULE `24 * (i + 1) = 24 * i + 24`]) THENL
           [UNDISCH_TAC `~(i + 1 < N)` THEN UNDISCH_TAC `i:num < N` THEN
            ARITH_TAC; ALL_TAC] THEN
          ASM_REWRITE_TAC[SUB_LIST_SPLIT; REJ_SAMPLE_APPEND; LENGTH_APPEND;
                          NUM_OF_WORDLIST_APPEND] THEN
          REWRITE_TAC[ADD_CLAUSES] THEN
          ABBREV_TAC
            `lr = LENGTH(REJ_SAMPLE(SUB_LIST(8*i,8) (inlist:(24 word)list)))` THEN
          SUBGOAL_THEN `lr <= 8` ASSUME_TAC THENL
           [EXPAND_TAC "lr" THEN REWRITE_TAC[REJ_SAMPLE] THEN
            TRANS_TAC LE_TRANS `LENGTH(MAP (\x:24 word. word(val x MOD 2 EXP 23):int32) (SUB_LIST(8*i,8) (inlist:(24 word)list)))` THEN
            REWRITE_TAC[LENGTH_FILTER; LENGTH_MAP; LENGTH_SUB_LIST] THEN
            ARITH_TAC;
            ALL_TAC] THEN
          SUBGOAL_THEN `248 < curlen + lr` ASSUME_TAC THENL
           [EXPAND_TAC "lr" THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
          FIRST_X_ASSUM(SUBST_ALL_TAC) THEN
          (fun (asl, w) ->
            try
              let newlen_eq_lr = snd(List.find (fun (_, th) ->
                let c = concl th in
                is_eq c &&
                (try fst(dest_var(lhs c)) = "newlen" with _ -> false) &&
                (try fst(dest_var(rhs c)) = "lr" with _ -> false)) asl) in
              RULE_ASSUM_TAC (REWRITE_RULE [newlen_eq_lr]) (asl, w)
            with _ -> ALL_TAC (asl, w)) THEN
          DISCARD_ASSUMPTIONS_TAC (fun th ->
            let c = concl th in
            let fvs = frees c in
            let has_const name t = try fst(dest_const t) = name with _ -> false in
            not(is_eq c &&
                can (find_term (has_const "read")) c &&
                can (find_term (has_const "bytes")) c) &&
            (not (forall (fun v -> type_of v = `:num`) fvs) ||
             exists (fun v -> let n = fst(dest_var v) in
               n = "N" || n = "newlen" || n = "curlist") fvs ||
             is_forall c)) THEN
          REPEAT CONJ_TAC THENL
           [MATCH_MP_TAC(TAUT `p ==> (if p then a else b) = a`) THEN
            REWRITE_TAC[NOT_CLAUSES; DE_MORGAN_THM;
                        VAL_WORD_ZX_GEN; VAL_WORD_SUB_CASES; VAL_WORD_ADD;
                        VAL_WORD; DIMINDEX_32; DIMINDEX_64] THEN
            CONV_TAC NUM_REDUCE_CONV THEN
            SUBGOAL_THEN `curlen < 4294967296 /\ lr < 4294967296 /\
                          curlen < 18446744073709551616 /\
                          lr < 18446744073709551616 /\
                          curlen + lr < 4294967296 /\
                          curlen + lr < 18446744073709551616`
              STRIP_ASSUME_TAC THENL
             [UNDISCH_TAC `curlen <= 248` THEN UNDISCH_TAC `lr <= 8` THEN
              ARITH_TAC; ALL_TAC] THEN
            SUBGOAL_THEN `248 <= curlen + lr` ASSUME_TAC THENL
             [UNDISCH_TAC `248 < curlen + lr` THEN ARITH_TAC; ALL_TAC] THEN
            SUBGOAL_THEN `(curlen + lr) - 248 < 18446744073709551616`
              ASSUME_TAC THENL
             [UNDISCH_TAC `curlen + lr < 18446744073709551616` THEN ARITH_TAC;
              ALL_TAC] THEN
            ASM_SIMP_TAC[MOD_LT; MOD_MOD_REFL] THEN
            UNDISCH_TAC `248 < curlen + lr` THEN ARITH_TAC;
            REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_ZX_GEN; VAL_WORD_ADD;
                        VAL_WORD; DIMINDEX_32; DIMINDEX_64] THEN
            CONV_TAC NUM_REDUCE_CONV THEN
            SUBGOAL_THEN `curlen < 4294967296 /\ lr < 4294967296 /\
                          curlen < 18446744073709551616 /\
                          lr < 18446744073709551616 /\
                          curlen + lr < 4294967296 /\
                          curlen + lr < 18446744073709551616`
              STRIP_ASSUME_TAC THENL
             [UNDISCH_TAC `curlen <= 248` THEN UNDISCH_TAC `lr <= 8` THEN
              ARITH_TAC; ALL_TAC] THEN
            ASM_SIMP_TAC[MOD_LT] THEN ARITH_TAC;
            REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_ZX_GEN; VAL_WORD_ADD;
                        VAL_WORD; DIMINDEX_32; DIMINDEX_64] THEN
            CONV_TAC NUM_REDUCE_CONV THEN
            UNDISCH_TAC `24 * i <= 808` THEN
            SPEC_TAC(`24 * i`,`n:num`) THEN GEN_TAC THEN DISCH_TAC THEN
            SUBGOAL_THEN `n < 4294967296 /\ n < 18446744073709551616 /\
                          n + 24 < 4294967296 /\
                          n + 24 < 18446744073709551616`
              STRIP_ASSUME_TAC THENL
             [UNDISCH_TAC `n <= 808` THEN ARITH_TAC; ALL_TAC] THEN
            ASM_SIMP_TAC[MOD_LT] THEN ARITH_TAC;
            REWRITE_TAC[DIMINDEX_32;
                        ARITH_RULE `4 * (curlen + lr) = 4 * curlen + 4 * lr`;
                        ARITH_RULE `32 * curlen = 8 * (4 * curlen)`] THEN
            REWRITE_TAC[MEMORY_BYTES_SPLIT] THEN
            ASM_REWRITE_TAC[] THEN
            REWRITE_TAC[EQ_ADD_LCANCEL; EQ_MULT_LCANCEL; EXP_EQ_0; ARITH_EQ] THEN
            ASM_REWRITE_TAC[] THEN NO_TAC];

          (* J1-B: JAE at s37 falls through to pc+111. VSTEPS 38-39 do CMP ecx/JA
             and exit to pc+181 because 808 < 24*(i+1) (from offset disjunct). *)
          ABBREV_TAC
            `lr = LENGTH(REJ_SAMPLE(SUB_LIST(8*i,8) (inlist:(24 word)list)))` THEN
          SUBGOAL_THEN `lr <= 8` ASSUME_TAC THENL
           [EXPAND_TAC "lr" THEN REWRITE_TAC[REJ_SAMPLE] THEN
            TRANS_TAC LE_TRANS `LENGTH(MAP (\x:24 word. word(val x MOD 2 EXP 23):int32) (SUB_LIST(8*i,8) (inlist:(24 word)list)))` THEN
            REWRITE_TAC[LENGTH_FILTER; LENGTH_MAP; LENGTH_SUB_LIST] THEN
            ARITH_TAC;
            ALL_TAC] THEN
          (* Resolve RIP s37 = word(pc + 111) via COND simplification *)
          SUBGOAL_THEN `read RIP s37 = word(pc + 111):int64` MP_TAC THENL
           [FIRST_X_ASSUM(fun th ->
              if can (find_term ((=) `read RIP s37`)) (concl th) &&
                 is_eq(concl th)
              then SUBST1_TAC th else failwith "") THEN
            MATCH_MP_TAC(TAUT `~p ==> (if p then a else b) = b`) THEN
            REWRITE_TAC[DE_MORGAN_THM; NOT_CLAUSES;
                        VAL_WORD_ZX_GEN; VAL_WORD_SUB_CASES; VAL_WORD_ADD;
                        VAL_WORD; DIMINDEX_32; DIMINDEX_64] THEN
            CONV_TAC NUM_REDUCE_CONV THEN
            SUBGOAL_THEN `curlen < 4294967296 /\ lr < 4294967296 /\
                          curlen < 18446744073709551616 /\
                          lr < 18446744073709551616 /\
                          curlen + lr < 4294967296 /\
                          curlen + lr < 18446744073709551616`
              STRIP_ASSUME_TAC THENL
             [UNDISCH_TAC `curlen <= 248` THEN UNDISCH_TAC `lr <= 8` THEN
              ARITH_TAC; ALL_TAC] THEN
            ASM_SIMP_TAC[MOD_LT; MOD_MOD_REFL] THEN
            UNDISCH_TAC
              `~(248 < curlen + LENGTH(REJ_SAMPLE(SUB_LIST(8*i,8) (inlist:(24 word)list))))`
              THEN
            EXPAND_TAC "lr" THEN ARITH_TAC;
            ALL_TAC] THEN
          DISCH_THEN ASSUME_TAC THEN
          FIRST_X_ASSUM(K ALL_TAC o check (fun th ->
            let c = concl th in
            can (find_term ((=) `read RIP s37`)) c && is_eq c &&
            can (find_term (fun t ->
              try fst(dest_const t) = "COND" with _ -> false)) (rhs c))) THEN
          X86_VSTEPS_TAC MLDSA_REJ_UNIFORM_EXEC (38--39) THEN
          (* Resolve RIP s39 = word(pc + 181) via JA analysis *)
          SUBGOAL_THEN `read RIP s39 = word(pc + 181):int64` MP_TAC THENL
           [FIRST_X_ASSUM(fun th ->
              if can (find_term ((=) `read RIP s39`)) (concl th) &&
                 is_eq(concl th)
              then SUBST1_TAC th else failwith "") THEN
            MATCH_MP_TAC(TAUT `p ==> (if p then a else b) = a`) THEN
            REWRITE_TAC[NOT_CLAUSES; DE_MORGAN_THM;
                        VAL_WORD_ZX_GEN; VAL_WORD_SUB_CASES; VAL_WORD_ADD;
                        VAL_WORD; DIMINDEX_32; DIMINDEX_64] THEN
            CONV_TAC NUM_REDUCE_CONV THEN
            SUBGOAL_THEN `24 * i < 4294967296 /\ 24 * i < 18446744073709551616 /\
                          24 * i + 24 < 4294967296 /\
                          24 * i + 24 < 18446744073709551616`
              STRIP_ASSUME_TAC THENL
             [UNDISCH_TAC `24 * i <= 808` THEN ARITH_TAC; ALL_TAC] THEN
            ASM_SIMP_TAC[MOD_LT; MOD_MOD_REFL] THEN
            UNDISCH_TAC `832 < 24 * (N + 1)` THEN
            UNDISCH_TAC `N = i + 1` THEN ARITH_TAC;
            ALL_TAC] THEN
          DISCH_THEN ASSUME_TAC THEN
          FIRST_X_ASSUM(K ALL_TAC o check (fun th ->
            let c = concl th in
            can (find_term ((=) `read RIP s39`)) c && is_eq c &&
            can (find_term (fun t ->
              try fst(dest_const t) = "COND" with _ -> false)) (rhs c))) THEN
          (* Rest mirrors J2's body, adapted for s39 *)
          SUBGOAL_THEN `newlen <= 8` ASSUME_TAC THENL
           [MP_TAC(ISPECL [`inlist:(24 word)list`; `i:num`; `curlist:int32 list`;
                           `curlen:num`] SIMD_ITERATION_BRIDGE) THEN
            ANTS_TAC THENL
             [ASM_REWRITE_TAC[] THEN
              UNDISCH_TAC `24 * (i + 1) <= 832` THEN ARITH_TAC;
              ALL_TAC] THEN
            STRIP_TAC THEN ASM_REWRITE_TAC[];
            ALL_TAC] THEN
          (fun (asl,w) ->
            try
              let has_const name t = try fst(dest_const t) = name with _ -> false in
              let has_var name t = try fst(dest_var t) = name with _ -> false in
              let b256_th = snd(find (fun (_,th) ->
                is_eq(concl th) &&
                can (find_term (has_const "bytes256")) (lhs(concl th)) &&
                not(can (find_term (has_const "MAYCHANGE")) (concl th))) asl) in
              let b256_state = find_term (fun t ->
                try let n = fst(dest_var t) in
                    String.length n > 1 && n.[0] = 's' && type_of t = `:x86state`
                with _ -> false) (lhs(concl b256_th)) in
              let b256_state_name = fst(dest_var b256_state) in
              let ymm_th = snd(find (fun (_,th) ->
                is_eq(concl th) && type_of(rhs(concl th)) = `:int256` &&
                can (find_term (has_const "YMM3")) (lhs(concl th)) &&
                can (find_term (has_var b256_state_name)) (lhs(concl th))) asl) in
              let b256_ymm3 = TRANS b256_th (SYM ymm_th) in
              let curlen_bound = snd(find (fun (_,th) ->
                try concl th = `curlen <= 248` with _ -> false) asl) in
              let vwe32 = CONV_RULE NUM_REDUCE_CONV
                (REWRITE_RULE[DIMINDEX_32] (INST_TYPE [`:32`,`:N`] VAL_WORD_EQ)) in
              let vwe64 = CONV_RULE NUM_REDUCE_CONV
                (REWRITE_RULE[DIMINDEX_64] (INST_TYPE [`:64`,`:N`] VAL_WORD_EQ)) in
              let cn32 = MATCH_MP vwe32 (CONV_RULE NUM_REDUCE_CONV
                (MATCH_MP (ARITH_RULE `n <= 248 ==> n < 4294967296`)
                  curlen_bound)) in
              let cn64 = MATCH_MP vwe64 (CONV_RULE NUM_REDUCE_CONV
                (MATCH_MP (ARITH_RULE `n <= 248 ==> n < 18446744073709551616`)
                  curlen_bound)) in
              let b256_norm = REWRITE_RULE[cn32; cn64] b256_ymm3 in
              let val_eq = AP_TERM `val:int256->num` b256_norm in
              let bytes32_eq = CONV_RULE(LAND_CONV(
                REWRITE_CONV[READ_COMPONENT_COMPOSE; VAL_READ_BYTES256] THENC
                REWRITE_CONV[GSYM READ_COMPONENT_COMPOSE])) val_eq in
              let vpermd_raw = snd(List.find (fun (_,th) ->
                is_eq(concl th) &&
                can (find_term (has_const "MOD")) (concl th) &&
                can (find_term (has_const "num_of_wordlist")) (concl th) &&
                can (find_term (has_var "newlen")) (concl th)) asl) in
              let is_ymm3_read th =
                is_eq(concl th) && type_of(rhs(concl th)) = `:int256` &&
                can (find_term (has_const "YMM3")) (lhs(concl th)) in
              let vpermd_states = List.filter (fun v ->
                let n = fst(dest_var v) in String.length n > 1 && n.[0] = 's' &&
                type_of v = `:x86state`) (frees(concl vpermd_raw)) in
              let vp_state_name = fst(dest_var(List.hd vpermd_states)) in
              let vpermd = try
                let ymm_b32 = snd(List.find (fun (_,th) ->
                  is_ymm3_read th &&
                  can (find_term (has_var b256_state_name))
                    (lhs(concl th))) asl) in
                let ymm_vp = snd(List.find (fun (_,th) ->
                  is_ymm3_read th &&
                  can (find_term (has_var vp_state_name))
                    (lhs(concl th))) asl) in
                let ymm_eq = TRANS ymm_b32 (SYM ymm_vp) in
                let val_eq = AP_TERM `val:int256->num` ymm_eq in
                REWRITE_RULE[GSYM val_eq] vpermd_raw
              with _ -> vpermd_raw in
              let newlen_bound = snd(List.find (fun (_,th) ->
                try is_binary "<=" (concl th) &&
                    (has_var "newlen" (lhand(concl th))) &&
                    dest_small_numeral(rand(concl th)) = 8
                with _ -> false) asl) in
              let bridge = MATCH_MP VPERMD_MEMORY_BRIDGE
                (CONJ bytes32_eq (CONJ vpermd newlen_bound)) in
              ASSUME_TAC bridge (asl,w)
            with _ -> failwith "J1-B PRE-ENSURES") THEN
          ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
          CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN ASM_REWRITE_TAC[] THEN
          SUBGOAL_THEN `N = i + 1` (fun th ->
            REWRITE_TAC[th; ARITH_RULE `8 * (i + 1) = 8 * i + 8`;
                           ARITH_RULE `24 * (i + 1) = 24 * i + 24`]) THENL
           [UNDISCH_TAC `~(i + 1 < N)` THEN UNDISCH_TAC `i:num < N` THEN
            ARITH_TAC; ALL_TAC] THEN
          ASM_REWRITE_TAC[SUB_LIST_SPLIT; REJ_SAMPLE_APPEND; LENGTH_APPEND;
                          NUM_OF_WORDLIST_APPEND] THEN
          REWRITE_TAC[ADD_CLAUSES] THEN
          (* lr already abbreviated in J1-B prologue *)
          ASM_REWRITE_TAC[] THEN
          REPEAT CONJ_TAC THENL
           [REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_ZX_GEN; VAL_WORD_ADD;
                        VAL_WORD; DIMINDEX_32; DIMINDEX_64] THEN
            CONV_TAC NUM_REDUCE_CONV THEN
            SUBGOAL_THEN `curlen < 4294967296 /\ lr < 4294967296 /\
                          curlen < 18446744073709551616 /\
                          lr < 18446744073709551616 /\
                          curlen + lr < 4294967296 /\
                          curlen + lr < 18446744073709551616`
              STRIP_ASSUME_TAC THENL
             [UNDISCH_TAC `curlen <= 248` THEN UNDISCH_TAC `lr <= 8` THEN
              ARITH_TAC; ALL_TAC] THEN
            ASM_SIMP_TAC[MOD_LT] THEN ARITH_TAC;
            REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_ZX_GEN; VAL_WORD_ADD;
                        VAL_WORD; DIMINDEX_32; DIMINDEX_64] THEN
            CONV_TAC NUM_REDUCE_CONV THEN
            UNDISCH_TAC `24 * i <= 808` THEN
            SPEC_TAC(`24 * i`,`n:num`) THEN GEN_TAC THEN DISCH_TAC THEN
            SUBGOAL_THEN `n < 4294967296 /\ n < 18446744073709551616 /\
                          n + 24 < 4294967296 /\
                          n + 24 < 18446744073709551616`
              STRIP_ASSUME_TAC THENL
             [UNDISCH_TAC `n <= 808` THEN ARITH_TAC; ALL_TAC] THEN
            ASM_SIMP_TAC[MOD_LT] THEN ARITH_TAC;
            REWRITE_TAC[DIMINDEX_32;
                        ARITH_RULE `4 * (curlen + lr) = 4 * curlen + 4 * lr`;
                        ARITH_RULE `32 * curlen = 8 * (4 * curlen)`] THEN
            REWRITE_TAC[MEMORY_BYTES_SPLIT] THEN
            ASM_REWRITE_TAC[] THEN
            REWRITE_TAC[EQ_ADD_LCANCEL; EQ_MULT_LCANCEL; EXP_EQ_0; ARITH_EQ] THEN
            (fun (asl, w) ->
              try
                let newlen_eq_lr = snd(List.find (fun (_, th) ->
                  let c = concl th in
                  is_eq c &&
                  (try fst(dest_var(lhs c)) = "newlen" with _ -> false) &&
                  (try fst(dest_var(rhs c)) = "lr" with _ -> false)) asl) in
                RULE_ASSUM_TAC (REWRITE_RULE [newlen_eq_lr]) (asl, w)
              with _ -> ALL_TAC (asl, w)) THEN
            ASM_REWRITE_TAC[] THEN NO_TAC]];
        (* J2: 248 < LENGTH(REJ_SAMPLE(SUB_LIST(0,8*N))): count exit *)
        (* Prelude: establish newlen <= 8, needed by PRE-ENSURES *)
        SUBGOAL_THEN `newlen <= 8` ASSUME_TAC THENL
         [MP_TAC(ISPECL [`inlist:(24 word)list`; `i:num`; `curlist:int32 list`;
                         `curlen:num`] SIMD_ITERATION_BRIDGE) THEN
          ANTS_TAC THENL
           [ASM_REWRITE_TAC[] THEN
            UNDISCH_TAC `24 * (i + 1) <= 832` THEN ARITH_TAC;
            ALL_TAC] THEN
          STRIP_TAC THEN ASM_REWRITE_TAC[];
          ALL_TAC] THEN
        (* PRE-ENSURES: derive full VPERMD bridge result before ENSURES_FINAL_STATE_TAC.
           Build: read(bytes(word_add res (word(4*curlen)), 4*newlen)) sN =
                  num_of_wordlist(REJ_SAMPLE(SUB_LIST(8*i,8) inlist))
           so that ASM_REWRITE_TAC can use it after ENSURES_FINAL_STATE_TAC *)
        (fun (asl,w) ->
          try
            let has_const name t = try fst(dest_const t) = name with _ -> false in
            let has_var name t = try fst(dest_var t) = name with _ -> false in
            (* 1. Derive bytes32 eq: read(bytes(addr,32)) sN = val(YMM3 sN) *)
            let b256_th = snd(find (fun (_,th) ->
              is_eq(concl th) &&
              can (find_term (has_const "bytes256")) (lhs(concl th)) &&
              not(can (find_term (has_const "MAYCHANGE")) (concl th))) asl) in
            let b256_state = find_term (fun t ->
              try let n = fst(dest_var t) in
                  String.length n > 1 && n.[0] = 's' && type_of t = `:x86state`
              with _ -> false) (lhs(concl b256_th)) in
            let b256_state_name = fst(dest_var b256_state) in
            let ymm_th = snd(find (fun (_,th) ->
              is_eq(concl th) && type_of(rhs(concl th)) = `:int256` &&
              can (find_term (has_const "YMM3")) (lhs(concl th)) &&
              can (find_term (has_var b256_state_name)) (lhs(concl th))) asl) in
            let b256_ymm3 = TRANS b256_th (SYM ymm_th) in
            let curlen_bound = snd(find (fun (_,th) ->
              try concl th = `curlen <= 248` with _ -> false) asl) in
            let vwe32 = CONV_RULE NUM_REDUCE_CONV
              (REWRITE_RULE[DIMINDEX_32] (INST_TYPE [`:32`,`:N`] VAL_WORD_EQ)) in
            let vwe64 = CONV_RULE NUM_REDUCE_CONV
              (REWRITE_RULE[DIMINDEX_64] (INST_TYPE [`:64`,`:N`] VAL_WORD_EQ)) in
            let cn32 = MATCH_MP vwe32 (CONV_RULE NUM_REDUCE_CONV
              (MATCH_MP (ARITH_RULE `n <= 248 ==> n < 4294967296`) curlen_bound)) in
            let cn64 = MATCH_MP vwe64 (CONV_RULE NUM_REDUCE_CONV
              (MATCH_MP (ARITH_RULE `n <= 248 ==> n < 18446744073709551616`) curlen_bound)) in
            let b256_norm = REWRITE_RULE[cn32; cn64] b256_ymm3 in
            let val_eq = AP_TERM `val:int256->num` b256_norm in
            let bytes32_eq = CONV_RULE(LAND_CONV(
              REWRITE_CONV[READ_COMPONENT_COMPOSE; VAL_READ_BYTES256] THENC
              REWRITE_CONV[GSYM READ_COMPONENT_COMPOSE])) val_eq in
            (* 2. Get VPERMD MOD hyp and bridge states *)
            let vpermd_raw = snd(List.find (fun (_,th) ->
              is_eq(concl th) &&
              can (find_term (has_const "MOD")) (concl th) &&
              can (find_term (has_const "num_of_wordlist")) (concl th) &&
              can (find_term (has_var "newlen")) (concl th)) asl) in
            let is_ymm3_read th =
              is_eq(concl th) && type_of(rhs(concl th)) = `:int256` &&
              can (find_term (has_const "YMM3")) (lhs(concl th)) in
            let vpermd_states = List.filter (fun v ->
              let n = fst(dest_var v) in String.length n > 1 && n.[0] = 's' &&
              type_of v = `:x86state`) (frees(concl vpermd_raw)) in
            let vp_state_name = fst(dest_var(List.hd vpermd_states)) in
            let vpermd = try
              let ymm_b32 = snd(List.find (fun (_,th) ->
                is_ymm3_read th &&
                can (find_term (has_var b256_state_name)) (lhs(concl th))) asl) in
              let ymm_vp = snd(List.find (fun (_,th) ->
                is_ymm3_read th &&
                can (find_term (has_var vp_state_name)) (lhs(concl th))) asl) in
              let ymm_eq = TRANS ymm_b32 (SYM ymm_vp) in
              REWRITE_RULE[GSYM(AP_TERM `val:int256->num` ymm_eq)] vpermd_raw
            with _ -> vpermd_raw in
            (* 3. Get newlen <= 8 *)
            let newlen_bound = snd(List.find (fun (_,th) ->
              try is_binary "<=" (concl th) &&
                  (has_var "newlen" (lhand(concl th))) &&
                  dest_small_numeral(rand(concl th)) = 8
              with _ -> false) asl) in
            (* 4. Forward chain VPERMD_MEMORY_BRIDGE *)
            let bridge = MATCH_MP VPERMD_MEMORY_BRIDGE
              (CONJ bytes32_eq (CONJ vpermd newlen_bound)) in
            Printf.printf "  J2 PRE-ENSURES: full bridge derived!\n%!";
            ASSUME_TAC bridge (asl,w)
          with e ->
            Printf.printf "  J2 PRE-ENSURES: failed at step (%s)\n%!" (Printexc.to_string e);
            (* Debug: count bytes256, res hyps *)
            let n_b256 = List.length (List.filter (fun (_,th) ->
              can (find_term (fun t -> try fst(dest_const t) = "bytes256" with _ -> false)) (concl th)) asl) in
            let n_res = List.length (List.filter (fun (_,th) ->
              can (find_term (fun t -> try fst(dest_var t) = "res" with _ -> false)) (concl th)) asl) in
            Printf.printf "  J2 PRE-ENSURES: %d bytes256 hyps, %d res hyps\n%!" n_b256 n_res;
            ALL_TAC (asl,w)) THEN
        ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
        CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN ASM_REWRITE_TAC[] THEN
        (* Substitute N = i+1 *)
        SUBGOAL_THEN `N = i + 1` (fun th ->
          REWRITE_TAC[th; ARITH_RULE `8 * (i + 1) = 8 * i + 8`;
                         ARITH_RULE `24 * (i + 1) = 24 * i + 24`]) THENL
         [UNDISCH_TAC `~(i + 1 < N)` THEN UNDISCH_TAC `i:num < N` THEN
          ARITH_TAC; ALL_TAC] THEN
        ASM_REWRITE_TAC[SUB_LIST_SPLIT; REJ_SAMPLE_APPEND; LENGTH_APPEND;
                        NUM_OF_WORDLIST_APPEND] THEN
        REWRITE_TAC[ADD_CLAUSES] THEN
        ABBREV_TAC `lr = LENGTH(REJ_SAMPLE(SUB_LIST(8*i,8) (inlist:(24 word)list)))` THEN
        SUBGOAL_THEN `lr <= 8` ASSUME_TAC THENL
         [EXPAND_TAC "lr" THEN REWRITE_TAC[REJ_SAMPLE] THEN
          TRANS_TAC LE_TRANS `LENGTH(MAP (\x:24 word. word(val x MOD 2 EXP 23):32 word) (SUB_LIST(8*i,8) (inlist:(24 word)list)))` THEN
          REWRITE_TAC[LENGTH_FILTER; LENGTH_MAP; LENGTH_SUB_LIST] THEN ARITH_TAC;
          ALL_TAC] THEN
        SUBGOAL_THEN `248 < curlen + lr` ASSUME_TAC THENL
         [FIRST_X_ASSUM(MP_TAC o check (fun th ->
            can (find_term (fun t -> try fst(dest_const t) = "REJ_SAMPLE" with _ -> false)) (concl th) &&
            can (find_term (fun t -> try dest_small_numeral t > 200 with _ -> false)) (concl th))) THEN
          SUBGOAL_THEN `N = i + 1` (fun th -> REWRITE_TAC[th; ARITH_RULE `8 * (i + 1) = 8 * i + 8`]) THENL
           [UNDISCH_TAC `~(i + 1 < N)` THEN UNDISCH_TAC `i:num < N` THEN ARITH_TAC;
            ALL_TAC] THEN
          ASM_REWRITE_TAC[SUB_LIST_SPLIT; REJ_SAMPLE_APPEND; LENGTH_APPEND] THEN
          REWRITE_TAC[ADD_CLAUSES] THEN EXPAND_TAC "lr" THEN ARITH_TAC;
          ALL_TAC] THEN
        FIRST_X_ASSUM(SUBST_ALL_TAC) THEN
        (* Rewrite bridge with newlen = lr BEFORE DISCARD eats the connection *)
        (fun (asl, w) ->
          try
            let newlen_eq_lr = snd(List.find (fun (_, th) ->
              let c = concl th in
              is_eq c &&
              (try fst(dest_var(lhs c)) = "newlen" with _ -> false) &&
              (try fst(dest_var(rhs c)) = "lr" with _ -> false)) asl) in
            RULE_ASSUM_TAC (REWRITE_RULE [newlen_eq_lr]) (asl, w)
          with _ -> ALL_TAC (asl, w)) THEN
        DISCARD_ASSUMPTIONS_TAC (fun th ->
          let c = concl th in
          let fvs = frees c in
          let has_const name t = try fst(dest_const t) = name with _ -> false in
          (* Keep: bridge (REJ_SAMPLE/read/bytes) AND invariant (read/bytes, curlist RHS) *)
          not(is_eq c &&
              can (find_term (has_const "read")) c &&
              can (find_term (has_const "bytes")) c) &&
          (not (forall (fun v -> type_of v = `:num`) fvs) ||
           exists (fun v -> let n = fst(dest_var v) in
             n = "N" || n = "newlen" || n = "curlist") fvs ||
           is_forall c)) THEN
        REPEAT CONJ_TAC THENL
         [(* 1. JA conditional.
             Use targeted UNDISCH instead of ASM_ARITH_TAC to avoid hanging
             on the ~200-assumption list. *)
          MATCH_MP_TAC(TAUT `p ==> (if p then a else b) = a`) THEN
          REWRITE_TAC[NOT_CLAUSES; DE_MORGAN_THM;
                      VAL_WORD_ZX_GEN; VAL_WORD_SUB_CASES; VAL_WORD_ADD;
                      VAL_WORD; DIMINDEX_32; DIMINDEX_64] THEN
          CONV_TAC NUM_REDUCE_CONV THEN
          SUBGOAL_THEN `curlen < 4294967296 /\ lr < 4294967296 /\
                        curlen < 18446744073709551616 /\ lr < 18446744073709551616 /\
                        curlen + lr < 4294967296 /\ curlen + lr < 18446744073709551616`
            STRIP_ASSUME_TAC THENL
           [UNDISCH_TAC `curlen <= 248` THEN UNDISCH_TAC `lr <= 8` THEN
            ARITH_TAC; ALL_TAC] THEN
          SUBGOAL_THEN `248 <= curlen + lr` ASSUME_TAC THENL
           [UNDISCH_TAC `248 < curlen + lr` THEN ARITH_TAC; ALL_TAC] THEN
          SUBGOAL_THEN `(curlen + lr) - 248 < 18446744073709551616` ASSUME_TAC THENL
           [UNDISCH_TAC `curlen + lr < 18446744073709551616` THEN ARITH_TAC;
            ALL_TAC] THEN
          ASM_SIMP_TAC[MOD_LT; MOD_MOD_REFL] THEN
          UNDISCH_TAC `248 < curlen + lr` THEN ARITH_TAC;
          (* 2. RAX *)
          REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_ZX_GEN; VAL_WORD_ADD;
                      VAL_WORD; DIMINDEX_32; DIMINDEX_64] THEN
          CONV_TAC NUM_REDUCE_CONV THEN
          SUBGOAL_THEN `curlen < 4294967296 /\ lr < 4294967296 /\
                        curlen < 18446744073709551616 /\ lr < 18446744073709551616 /\
                        curlen + lr < 4294967296 /\ curlen + lr < 18446744073709551616`
            STRIP_ASSUME_TAC THENL
           [UNDISCH_TAC `curlen <= 248` THEN UNDISCH_TAC `lr <= 8` THEN
            ARITH_TAC; ALL_TAC] THEN
          ASM_SIMP_TAC[MOD_LT] THEN ARITH_TAC;
          (* 3. RCX *)
          REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_ZX_GEN; VAL_WORD_ADD;
                      VAL_WORD; DIMINDEX_32; DIMINDEX_64] THEN
          CONV_TAC NUM_REDUCE_CONV THEN
          UNDISCH_TAC `24 * i <= 808` THEN
          SPEC_TAC(`24 * i`,`n:num`) THEN GEN_TAC THEN DISCH_TAC THEN
          SUBGOAL_THEN `n < 4294967296 /\ n < 18446744073709551616 /\
                        n + 24 < 4294967296 /\ n + 24 < 18446744073709551616`
            STRIP_ASSUME_TAC THENL
           [UNDISCH_TAC `n <= 808` THEN ARITH_TAC; ALL_TAC] THEN
          ASM_SIMP_TAC[MOD_LT] THEN ARITH_TAC;
          (* 4. Memory store — bridge theorem from PRE-ENSURES is in assumptions *)
          (fun gl -> Printf.printf "  MEMSTORE(J2): using bridge from PRE-ENSURES\n%!"; ALL_TAC gl) THEN
          REWRITE_TAC[DIMINDEX_32;
                      ARITH_RULE `4 * (curlen + lr) = 4 * curlen + 4 * lr`;
                      ARITH_RULE `32 * curlen = 8 * (4 * curlen)`] THEN
          REWRITE_TAC[MEMORY_BYTES_SPLIT] THEN
          ASM_REWRITE_TAC[] THEN
          REWRITE_TAC[EQ_ADD_LCANCEL; EQ_MULT_LCANCEL; EXP_EQ_0; ARITH_EQ] THEN
          ASM_REWRITE_TAC[] THEN NO_TAC]]];

    (* ================================================================= *)
    (* Subgoal 3: Post-loop                                              *)
    (* ================================================================= *)
    (fun gl -> Printf.printf "  DEBUG[K]: post-loop\n%!"; ALL_TAC gl) THEN
    (* ================================================================= *)
    (* Subgoal 3: Post-loop (scalar loop + VZEROUPPER + RET)             *)
    (*                                                                   *)
    (* Entry: pc+181 with REJ_SAMPLE(SUB_LIST(0,8*N)) accumulated.      *)
    (* Code structure:                                                  *)
    (*   pc+181: CMP eax,256; JAE vzeroupper                           *)
    (*   pc+188: CMP ecx,837; JA vzeroupper                            *)
    (*   pc+196..240: scalar coefficient loop (≤ 8 iterations)         *)
    (*   pc+242: VZEROUPPER                                             *)
    (*                                                                   *)
    (* Preparation: abbreviate outlist/outlen, establish bounds.        *)
    (* ================================================================= *)
    CONV_TAC(RATOR_CONV(LAND_CONV(TOP_DEPTH_CONV let_CONV))) THEN
    MAP_EVERY ABBREV_TAC
     [`outlist = REJ_SAMPLE (SUB_LIST (0,8 * N) inlist)`;
      `outlen = LENGTH(outlist:int32 list)`] THEN
    (* Save LENGTH(REJ_SAMPLE(...)) = outlen before ABBREV consumes the connection *)
    SUBGOAL_THEN
     `LENGTH(REJ_SAMPLE(SUB_LIST(0, 8 * N) (inlist:(24 word)list))) = outlen`
     ASSUME_TAC THENL
     [UNDISCH_TAC `REJ_SAMPLE (SUB_LIST (0,8 * N) (inlist:(24 word)list)) = outlist` THEN
      DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
      UNDISCH_TAC `LENGTH (outlist:int32 list) = outlen` THEN
      DISCH_THEN(fun th -> REWRITE_TAC[th]);
      ALL_TAC] THEN
    (* Derive 24*N <= 832 and LENGTH(REJ_SAMPLE(SUB_LIST(0, 8*(N-1)))) <= 248 *)
    SUBGOAL_THEN
     `24 * N <= 832 /\
      LENGTH(REJ_SAMPLE(SUB_LIST(0, 8 * (N - 1)) (inlist:(24 word)list))) <= 248`
     STRIP_ASSUME_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o SPEC `N - 1`) THEN
      ANTS_TAC THENL [UNDISCH_TAC `~(N = 0)` THEN ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `(N - 1) + 1 = N` SUBST1_TAC THENL
       [UNDISCH_TAC `~(N = 0)` THEN ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[];
      ALL_TAC] THEN
    (* Derive outlen <= 256 via SIMD_ITERATION_BRIDGE at (N-1) *)
    SUBGOAL_THEN `outlen <= 256` ASSUME_TAC THENL
     [MP_TAC(ISPECL [`inlist:(24 word)list`; `N - 1`;
                     `REJ_SAMPLE(SUB_LIST(0, 8*(N-1)) (inlist:(24 word)list))`;
                     `LENGTH(REJ_SAMPLE(SUB_LIST(0, 8*(N-1)) (inlist:(24 word)list)))`]
        SIMD_ITERATION_BRIDGE) THEN
      ANTS_TAC THENL
       [REWRITE_TAC[] THEN
        SUBGOAL_THEN `N - 1 + 1 = N` SUBST1_TAC THENL
         [UNDISCH_TAC `~(N = 0)` THEN ARITH_TAC; ALL_TAC] THEN
        UNDISCH_TAC `LENGTH (inlist:(24 word)list) = 280` THEN
        UNDISCH_TAC `24 * N <= 832` THEN ARITH_TAC;
        ALL_TAC] THEN
      SUBGOAL_THEN `N - 1 + 1 = N` SUBST1_TAC THENL
       [UNDISCH_TAC `~(N = 0)` THEN ARITH_TAC; ALL_TAC] THEN
      STRIP_TAC THEN
      UNDISCH_TAC
        `LENGTH(REJ_SAMPLE(SUB_LIST(0, 8 * N) (inlist:(24 word)list))) = outlen` THEN
      UNDISCH_TAC
        `LENGTH (REJ_SAMPLE (SUB_LIST (0,8 * N) (inlist:(24 word)list))) =
         LENGTH (REJ_SAMPLE (SUB_LIST (0,8 * (N - 1)) inlist)) +
         LENGTH (REJ_SAMPLE (SUB_LIST (8 * (N - 1),8) inlist))` THEN
      UNDISCH_TAC
        `LENGTH (REJ_SAMPLE (SUB_LIST (0,8 * (N - 1)) (inlist:(24 word)list))) <= 248` THEN
      UNDISCH_TAC
        `LENGTH (REJ_SAMPLE (SUB_LIST (8 * (N - 1),8) (inlist:(24 word)list))) <= 8` THEN
      ARITH_TAC;
      ALL_TAC] THEN
    (* Characterize the number of scalar iterations K via WOP.
       K = smallest j such that LENGTH(REJ_SAMPLE(SUB_LIST(0,8*N+j))) >= 256 OR 837 < 24*N+3*j. *)
    SUBGOAL_THEN
      `?j. 256 <= LENGTH(REJ_SAMPLE(SUB_LIST(0, 8 * N + j) (inlist:(24 word)list))) \/
           837 < 24 * N + 3 * j`
      MP_TAC THENL
     [EXISTS_TAC `280:num` THEN DISJ2_TAC THEN
      UNDISCH_TAC `24 * N <= 832` THEN ARITH_TAC;
      GEN_REWRITE_TAC LAND_CONV [num_WOP]] THEN
    DISCH_THEN(X_CHOOSE_THEN `K:num` (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
    DISCH_THEN(fun th ->
      ASSUME_TAC(REWRITE_RULE[DE_MORGAN_THM; NOT_LE; NOT_LT] th)) THEN
    (* Case split: K = 0 (no scalar iterations) vs K > 0 (scalar loop) *)
    ASM_CASES_TAC `K = 0` THENL
     [(* K = 0: Must have outlen = 256 (since 24*N <= 832 rules out offset exit at K=0). *)
      SUBGOAL_THEN `outlen = 256` ASSUME_TAC THENL
       [RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `K = 0`; ADD_CLAUSES; MULT_CLAUSES]) THEN
        UNDISCH_TAC
          `256 <= LENGTH (REJ_SAMPLE (SUB_LIST (0,8 * N) (inlist:(24 word)list))) \/
           837 < 24 * N` THEN
        UNDISCH_TAC
          `LENGTH(REJ_SAMPLE(SUB_LIST(0, 8 * N) (inlist:(24 word)list))) = outlen` THEN
        DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
        UNDISCH_TAC `outlen <= 256` THEN
        UNDISCH_TAC `24 * N <= 832` THEN ARITH_TAC;
        ALL_TAC] THEN
      (* Apply case A proof: JAE fires to pc+242 *)
      ENSURES_INIT_TAC "s0" THEN
      X86_STEPS_TAC MLDSA_REJ_UNIFORM_EXEC [40;41] THEN
      RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `outlen = 256`]) THEN
      FIRST_X_ASSUM(fun th ->
        if (try let s = string_of_term (concl th) in String.length s > 20 &&
                String.sub s 0 11 = "read RIP s4" with _ -> false) &&
           is_eq(concl th)
        then ASSUME_TAC(CONV_RULE(RAND_CONV(DEPTH_CONV WORD_NUM_RED_CONV)) th)
        else failwith "not RIP") THEN
      X86_STEPS_TAC MLDSA_REJ_UNIFORM_EXEC [55] THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
      CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
      SUBGOAL_THEN `SUB_LIST (0,256) (REJ_SAMPLE (inlist:(24 word)list)) =
                    REJ_SAMPLE (SUB_LIST (0, 8 * N) inlist)`
        ASSUME_TAC THENL
       [MATCH_MP_TAC REJ_SAMPLE_PREFIX_256 THEN ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC
        `REJ_SAMPLE (SUB_LIST (0,8 * N) (inlist:(24 word)list)) = outlist` THEN
      DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
      UNDISCH_TAC `LENGTH (outlist:int32 list) = outlen` THEN
      DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
      ASM_REWRITE_TAC[];

      (* K > 0: scalar loop runs K times. Use ENSURES_WHILE_UP2_TAC. *)
      ENSURES_WHILE_UP2_TAC `K:num` `pc + 181` `pc + 242`
        `\i s. bytes_loaded s (word pc) (BUTLAST mldsa_rej_uniform_tmc) /\
               read RSP s = stackpointer /\
               read (memory :> bytes (buf,840)) s = num_of_wordlist inlist /\
               read (memory :> bytes (table,2048)) s =
                 num_of_wordlist(mldsa_rej_uniform_table:byte list) /\
               read RDI s = res /\ read RSI s = buf /\ read RDX s = table /\
               read YMM0 s =
                 word 115366376096492355175489748997433888275274855593258845241081954797768348401920 /\
               read YMM1 s =
                 word 226156397384342666605459106258636701594091082888230722833791023177481060351 /\
               read YMM2 s =
                 word 225935595421087293402315996791205668696012104344015382954355885915737415681 /\
               (let outlist_i = REJ_SAMPLE(SUB_LIST(0, 8 * N + i) (inlist:(24 word)list)) in
                let outlen_i = LENGTH outlist_i in
                read RAX s = word outlen_i /\
                read RCX s = word(24 * N + 3 * i) /\
                read(memory :> bytes(res, 4 * outlen_i)) s = num_of_wordlist outlist_i)` THEN
      ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
       [(* Init: precond -> invariant @ 0 *)
        ENSURES_INIT_TAC "s0" THEN
        ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
        CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
        REWRITE_TAC[ADD_CLAUSES; MULT_CLAUSES] THEN ASM_REWRITE_TAC[];

        (* Body: invariant @ i -> invariant @ (i+1) at pc+181 or pc+242.
           Steps CMP eax 256; JAE (not taken), CMP ecx 837; JA (not taken),
           then scalar body (MOVZX + mask + CMP Q + JAE), then accept/reject branches.
           Currently this whole body is CHEAT'd — TODO. *)
        REPEAT CHEAT_TAC;

        (* Post: invariant @ K -> postcondition.
           At i=K, exit condition fires. RIP = pc+242 (vzeroupper). *)
        ENSURES_INIT_TAC "s0" THEN
        (* Break out the invariant conjunction *)
        RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV let_CONV)) THEN
        FIRST_X_ASSUM(fun th ->
          let c = concl th in
          if is_conj c && (try can (find_term ((=) `LENGTH (REJ_SAMPLE (SUB_LIST (0,8 * N + K) (inlist:(24 word)list)))`)) c with _ -> false)
          then STRIP_ASSUME_TAC th else failwith "not inv") THEN
        (* VZEROUPPER *)
        X86_STEPS_TAC MLDSA_REJ_UNIFORM_EXEC [55] THEN
        ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
        CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
        (* The disjunct at K: either count-exit (256 <= outlen_K) or offset-exit (837 < 24*N+3*K) *)
        FIRST_X_ASSUM(DISJ_CASES_TAC o check (is_disj o concl)) THENL
         [(* count-exit case: 256 <= outlen_K. Since outlen is monotonic +0/+1 per scalar iter,
             and outlen_{K-1} < 256 (from WOP), we have outlen_K = 256. *)
          SUBGOAL_THEN
            `LENGTH (REJ_SAMPLE (SUB_LIST (0,8 * N + K) (inlist:(24 word)list))) = 256`
            ASSUME_TAC THENL
           [REPEAT CHEAT_TAC;  (* TODO: monotonicity (outlen increases by 0 or 1 per iter) *)
            ALL_TAC] THEN
          SUBGOAL_THEN `SUB_LIST (0,256) (REJ_SAMPLE (inlist:(24 word)list)) =
                        REJ_SAMPLE (SUB_LIST (0, 8 * N + K) inlist)`
            ASSUME_TAC THENL
           [MATCH_MP_TAC REJ_SAMPLE_PREFIX_256 THEN ASM_REWRITE_TAC[];
            ALL_TAC] THEN
          ASM_REWRITE_TAC[] THEN
          SUBGOAL_THEN `SUB_LIST (0,256) (REJ_SAMPLE (SUB_LIST (0,8 * N + K) (inlist:(24 word)list))) =
                        REJ_SAMPLE (SUB_LIST (0,8 * N + K) inlist)`
            SUBST1_TAC THENL
           [MATCH_MP_TAC SUB_LIST_REFL THEN ASM_REWRITE_TAC[LE_REFL];
            ALL_TAC] THEN
          ASM_REWRITE_TAC[];

          (* offset-exit case: 837 < 24*N+3*K. Need to handle whether count-exit also fires. *)
          ASM_CASES_TAC
            `256 <= LENGTH(REJ_SAMPLE(SUB_LIST(0, 8 * N + K) (inlist:(24 word)list)))`
          THENL
           [(* Both conditions: 256 <= outlen_K, reuse SUBLIST_256_BOUNDED *)
            SUBGOAL_THEN `SUB_LIST (0,256) (REJ_SAMPLE (inlist:(24 word)list)) =
                          SUB_LIST (0,256) (REJ_SAMPLE (SUB_LIST (0, 8 * N + K) inlist))`
              ASSUME_TAC THENL
             [MATCH_MP_TAC REJ_SAMPLE_SUBLIST_256_BOUNDED THEN ASM_REWRITE_TAC[];
              ALL_TAC] THEN
            REPEAT CHEAT_TAC;  (* TODO: memory subsume for case when outlen_K > 256 *)

            (* Only offset-exit: outlen_K < 256 and 24*N+3*K > 837.
               Then 8*N+K >= 280 (bytes consumed past input), so SUB_LIST = inlist. *)
            SUBGOAL_THEN `SUB_LIST (0, 8 * N + K) (inlist:(24 word)list) = inlist`
              SUBST1_TAC THENL
             [MATCH_MP_TAC SUB_LIST_REFL THEN
              UNDISCH_TAC `LENGTH (inlist:(24 word)list) = 280` THEN
              UNDISCH_TAC `837 < 24 * N + 3 * K` THEN ARITH_TAC;
              ALL_TAC] THEN
            SUBGOAL_THEN `LENGTH (REJ_SAMPLE (inlist:(24 word)list)) <= 256`
              ASSUME_TAC THENL
             [UNDISCH_TAC
                `~(256 <= LENGTH (REJ_SAMPLE (SUB_LIST (0,8 * N + K) (inlist:(24 word)list))))` THEN
              SUBGOAL_THEN `SUB_LIST (0, 8 * N + K) (inlist:(24 word)list) = inlist`
                SUBST1_TAC THENL
               [MATCH_MP_TAC SUB_LIST_REFL THEN
                UNDISCH_TAC `LENGTH (inlist:(24 word)list) = 280` THEN
                UNDISCH_TAC `837 < 24 * N + 3 * K` THEN ARITH_TAC;
                ALL_TAC] THEN
              ARITH_TAC;
              ALL_TAC] THEN
            SUBGOAL_THEN `SUB_LIST (0,256) (REJ_SAMPLE (inlist:(24 word)list)) = REJ_SAMPLE inlist`
              SUBST1_TAC THENL
             [MATCH_MP_TAC SUB_LIST_REFL THEN ASM_REWRITE_TAC[];
              ALL_TAC] THEN
            REWRITE_TAC[] THEN
            UNDISCH_TAC
              `read (memory :> bytes (res,4 * LENGTH (REJ_SAMPLE (SUB_LIST (0,8 * N + K) (inlist:(24 word)list)))))
                s0 = num_of_wordlist (REJ_SAMPLE (SUB_LIST (0,8 * N + K) inlist))` THEN
            SUBGOAL_THEN `SUB_LIST (0, 8 * N + K) (inlist:(24 word)list) = inlist`
              SUBST1_TAC THENL
             [MATCH_MP_TAC SUB_LIST_REFL THEN
              UNDISCH_TAC `LENGTH (inlist:(24 word)list) = 280` THEN
              UNDISCH_TAC `837 < 24 * N + 3 * K` THEN ARITH_TAC;
              ALL_TAC] THEN
            REWRITE_TAC[]]]]]]);;
(* DISABLED: original count exit + post-loop for debugging *)
(* ORIGINAL_J2:
        (* The first JA fires because curlen + newlen > 248 *)
        ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
        CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN ASM_REWRITE_TAC[] THEN
        (* Resolve the JA conditional: prove curlen + newlen > 248 *)
        (* Key fact: curlen + newlen = LENGTH(REJ_SAMPLE(SUB_LIST(0,8*N))) > 248 *)
        SUBGOAL_THEN `248 < curlen + LENGTH(REJ_SAMPLE(SUB_LIST(8*i,8) (inlist:(24 word)list)))`
          ASSUME_TAC THENL
         [MP_TAC(ASSUME `248 < LENGTH(REJ_SAMPLE(SUB_LIST(0,8 * N) inlist))`) THEN
          SUBGOAL_THEN `N = i + 1`
            (fun th -> REWRITE_TAC[th; ARITH_RULE `8 * (i + 1) = 8 * i + 8`]) THENL
           [UNDISCH_TAC `~(i + 1 < N)` THEN UNDISCH_TAC `i:num < N` THEN ARITH_TAC;
            ALL_TAC] THEN
          ASM_REWRITE_TAC[SUB_LIST_SPLIT; REJ_SAMPLE_APPEND; LENGTH_APPEND;
                          ADD_CLAUSES] THEN
          ARITH_TAC;
          ALL_TAC] THEN
        (* Use the bound to resolve the JA word comparison.
           Generalize over curlen and newlen to pure arithmetic. *)
        ABBREV_TAC `lr = LENGTH(REJ_SAMPLE(SUB_LIST(8*i,8) (inlist:(24 word)list)))` THEN
        UNDISCH_TAC `248 < curlen + lr` THEN
        UNDISCH_TAC `curlen <= 248` THEN
        SUBGOAL_THEN `lr <= 8` MP_TAC THENL
         [EXPAND_TAC "lr" THEN
          MP_TAC(ISPECL [`inlist:(24 word)list`; `i:num`; `curlist:int32 list`; `curlen:num`]
            SIMD_ITERATION_BRIDGE) THEN
          ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[];
          ALL_TAC] THEN
        (* Generalize to pure arithmetic, then resolve word comparison *)
        SPEC_TAC(`lr:num`, `lr:num`) THEN GEN_TAC THEN
        SPEC_TAC(`curlen:num`, `c:num`) THEN GEN_TAC THEN
        REPEAT DISCH_TAC THEN
        REWRITE_TAC[NOT_CLAUSES; DE_MORGAN_THM] THEN
        REWRITE_TAC[VAL_WORD_ZX_GEN; VAL_WORD_SUB_CASES; VAL_WORD_ADD;
                    VAL_WORD; DIMINDEX_32; DIMINDEX_64] THEN
        CONV_TAC NUM_REDUCE_CONV THEN
        SUBGOAL_THEN `c MOD 4294967296 = c /\ lr MOD 4294967296 = lr`
          (fun th -> REWRITE_TAC[th]) THENL
         [CONJ_TAC THEN MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC; ALL_TAC] THEN
        SUBGOAL_THEN `c MOD 18446744073709551616 = c /\
                      lr MOD 18446744073709551616 = lr`
          (fun th -> REWRITE_TAC[th]) THENL
         [CONJ_TAC THEN MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC; ALL_TAC] THEN
        SUBGOAL_THEN `(c + lr) MOD 18446744073709551616 = c + lr`
          (fun th -> REWRITE_TAC[th]) THENL
         [MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC; ALL_TAC] THEN
        REWRITE_TAC[MOD_MOD_REFL] THEN
        SUBGOAL_THEN `248 <= c + lr` ASSUME_TAC THENL
         [ASM_ARITH_TAC; ALL_TAC] THEN
        ASM_REWRITE_TAC[] THEN
        CONJ_TAC THENL
         [MATCH_MP_TAC REAL_OF_NUM_SUB THEN ASM_REWRITE_TAC[];
          ASM_ARITH_TAC]]];

    (fun gl -> Printf.printf "  DEBUG[K]: reached post-loop section\n%!"; ALL_TAC gl) THEN
    (* ================================================================= *)
    (* Subgoal 3: Post-loop (scalar loop + VZEROUPPER + RET)             *)
    (*                                                                   *)
    (* Entry: pc+181 with REJ_SAMPLE(SUB_LIST(0,8*N)) accumulated.      *)
    (* Code: CMP eax,256; JNB vzeroupper                                 *)
    (*        CMP ecx,837; JA vzeroupper                                 *)
    (*        scalar coefficient loop (MOVZX+SHL+OR+AND+CMP+JNB+MOV)    *)
    (*        VZEROUPPER; (implicit RET via BUTLAST)                     *)
    (* ================================================================= *)
    CONV_TAC(RATOR_CONV(LAND_CONV(TOP_DEPTH_CONV let_CONV))) THEN
    MAP_EVERY ABBREV_TAC
     [`outlist = REJ_SAMPLE (SUB_LIST (0,8 * N) inlist)`;
      `outlen = LENGTH(outlist:int32 list)`] THEN
    (* Bound outlen for word arithmetic *)
    SUBGOAL_THEN `outlen <= 280` ASSUME_TAC THENL
     [EXPAND_TAC "outlen" THEN EXPAND_TAC "outlist" THEN
      REWRITE_TAC[REJ_SAMPLE] THEN
      W(MP_TAC o PART_MATCH lhand LENGTH_FILTER o lhand o snd) THEN
      MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] LE_TRANS) THEN
      REWRITE_TAC[LENGTH_MAP; LENGTH_SUB_LIST] THEN
      ASM_ARITH_TAC;
      ALL_TAC] THEN
    CHEAT_TAC  --- end of disabled code *)
