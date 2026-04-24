(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Use hint to correct high bits of decomposition (ML-DSA, param 44).        *)
(* ========================================================================= *)

needs "arm/proofs/base.ml";;
needs "common/mlkem_mldsa.ml";;

(**** print_literal_from_elf "arm/mldsa/mldsa_poly_use_hint_88.o";;
 ****)

let mldsa_poly_use_hint_88_mc = define_assert_from_elf
 "mldsa_poly_use_hint_88_mc" "arm/mldsa/mldsa_poly_use_hint_88.o"
(*** BYTECODE START ***)
[
  0x529c0024;       (* arm_MOV W4 (rvalue (word 57345)) *)
  0x72a00fe4;       (* arm_MOVK W4 (word 127) 16 *)
  0x4e040c94;       (* arm_DUP_GEN Q20 X4 32 128 *)
  0x528d8005;       (* arm_MOV W5 (rvalue (word 27648)) *)
  0x72a00fc5;       (* arm_MOVK W5 (word 126) 16 *)
  0x4e040cb5;       (* arm_DUP_GEN Q21 X5 32 128 *)
  0x529d0007;       (* arm_MOV W7 (rvalue (word 59392)) *)
  0x72a00047;       (* arm_MOVK W7 (word 2) 16 *)
  0x4e040cf6;       (* arm_DUP_GEN Q22 X7 32 128 *)
  0x5280b02b;       (* arm_MOV W11 (rvalue (word 1409)) *)
  0x72ab02cb;       (* arm_MOVK W11 (word 22550) 16 *)
  0x4e040d77;       (* arm_DUP_GEN Q23 X11 32 128 *)
  0x4f010578;       (* arm_MOVI Q24 (word 184683593771) *)
  0xd2800203;       (* arm_MOV X3 (rvalue (word 16)) *)
  0x3dc00421;       (* arm_LDR Q1 X1 (Immediate_Offset (word 16)) *)
  0x3dc00822;       (* arm_LDR Q2 X1 (Immediate_Offset (word 32)) *)
  0x3dc00c23;       (* arm_LDR Q3 X1 (Immediate_Offset (word 48)) *)
  0x3cc40420;       (* arm_LDR Q0 X1 (Postimmediate_Offset (word 64)) *)
  0x3dc00445;       (* arm_LDR Q5 X2 (Immediate_Offset (word 16)) *)
  0x3dc00846;       (* arm_LDR Q6 X2 (Immediate_Offset (word 32)) *)
  0x3dc00c47;       (* arm_LDR Q7 X2 (Immediate_Offset (word 48)) *)
  0x3cc40444;       (* arm_LDR Q4 X2 (Postimmediate_Offset (word 64)) *)
  0x4eb7b431;       (* arm_SQDMULH_VEC Q17 Q1 Q23 32 128 *)
  0x4f2f2631;       (* arm_SRSHR_VEC Q17 Q17 17 32 128 *)
  0x4eb53439;       (* arm_CMGT_VEC Q25 Q1 Q21 32 128 *)
  0x6eb69621;       (* arm_MLS_VEC Q1 Q17 Q22 32 128 *)
  0x4e791e31;       (* arm_BIC_VEC Q17 Q17 Q25 128 *)
  0x4eb98421;       (* arm_ADD_VEC Q1 Q1 Q25 32 128 *)
  0x6ea09821;       (* arm_CMLE_VEC_ZERO Q1 Q1 32 128 *)
  0x4f001421;       (* arm_ORR_VEC Q1 Q1 (rvalue (word 79228162532711081671548469249)) 128 *)
  0x4ea59431;       (* arm_MLA_VEC Q17 Q1 Q5 32 128 *)
  0x4eb83639;       (* arm_CMGT_VEC Q25 Q17 Q24 32 128 *)
  0x4e791e31;       (* arm_BIC_VEC Q17 Q17 Q25 128 *)
  0x6eb86e31;       (* arm_UMIN_VEC Q17 Q17 Q24 32 128 *)
  0x4eb7b452;       (* arm_SQDMULH_VEC Q18 Q2 Q23 32 128 *)
  0x4f2f2652;       (* arm_SRSHR_VEC Q18 Q18 17 32 128 *)
  0x4eb53459;       (* arm_CMGT_VEC Q25 Q2 Q21 32 128 *)
  0x6eb69642;       (* arm_MLS_VEC Q2 Q18 Q22 32 128 *)
  0x4e791e52;       (* arm_BIC_VEC Q18 Q18 Q25 128 *)
  0x4eb98442;       (* arm_ADD_VEC Q2 Q2 Q25 32 128 *)
  0x6ea09842;       (* arm_CMLE_VEC_ZERO Q2 Q2 32 128 *)
  0x4f001422;       (* arm_ORR_VEC Q2 Q2 (rvalue (word 79228162532711081671548469249)) 128 *)
  0x4ea69452;       (* arm_MLA_VEC Q18 Q2 Q6 32 128 *)
  0x4eb83659;       (* arm_CMGT_VEC Q25 Q18 Q24 32 128 *)
  0x4e791e52;       (* arm_BIC_VEC Q18 Q18 Q25 128 *)
  0x6eb86e52;       (* arm_UMIN_VEC Q18 Q18 Q24 32 128 *)
  0x4eb7b473;       (* arm_SQDMULH_VEC Q19 Q3 Q23 32 128 *)
  0x4f2f2673;       (* arm_SRSHR_VEC Q19 Q19 17 32 128 *)
  0x4eb53479;       (* arm_CMGT_VEC Q25 Q3 Q21 32 128 *)
  0x6eb69663;       (* arm_MLS_VEC Q3 Q19 Q22 32 128 *)
  0x4e791e73;       (* arm_BIC_VEC Q19 Q19 Q25 128 *)
  0x4eb98463;       (* arm_ADD_VEC Q3 Q3 Q25 32 128 *)
  0x6ea09863;       (* arm_CMLE_VEC_ZERO Q3 Q3 32 128 *)
  0x4f001423;       (* arm_ORR_VEC Q3 Q3 (rvalue (word 79228162532711081671548469249)) 128 *)
  0x4ea79473;       (* arm_MLA_VEC Q19 Q3 Q7 32 128 *)
  0x4eb83679;       (* arm_CMGT_VEC Q25 Q19 Q24 32 128 *)
  0x4e791e73;       (* arm_BIC_VEC Q19 Q19 Q25 128 *)
  0x6eb86e73;       (* arm_UMIN_VEC Q19 Q19 Q24 32 128 *)
  0x4eb7b410;       (* arm_SQDMULH_VEC Q16 Q0 Q23 32 128 *)
  0x4f2f2610;       (* arm_SRSHR_VEC Q16 Q16 17 32 128 *)
  0x4eb53419;       (* arm_CMGT_VEC Q25 Q0 Q21 32 128 *)
  0x6eb69600;       (* arm_MLS_VEC Q0 Q16 Q22 32 128 *)
  0x4e791e10;       (* arm_BIC_VEC Q16 Q16 Q25 128 *)
  0x4eb98400;       (* arm_ADD_VEC Q0 Q0 Q25 32 128 *)
  0x6ea09800;       (* arm_CMLE_VEC_ZERO Q0 Q0 32 128 *)
  0x4f001420;       (* arm_ORR_VEC Q0 Q0 (rvalue (word 79228162532711081671548469249)) 128 *)
  0x4ea49410;       (* arm_MLA_VEC Q16 Q0 Q4 32 128 *)
  0x4eb83619;       (* arm_CMGT_VEC Q25 Q16 Q24 32 128 *)
  0x4e791e10;       (* arm_BIC_VEC Q16 Q16 Q25 128 *)
  0x6eb86e10;       (* arm_UMIN_VEC Q16 Q16 Q24 32 128 *)
  0x3d800411;       (* arm_STR Q17 X0 (Immediate_Offset (word 16)) *)
  0x3d800812;       (* arm_STR Q18 X0 (Immediate_Offset (word 32)) *)
  0x3d800c13;       (* arm_STR Q19 X0 (Immediate_Offset (word 48)) *)
  0x3c840410;       (* arm_STR Q16 X0 (Postimmediate_Offset (word 64)) *)
  0xf1000463;       (* arm_SUBS X3 X3 (rvalue (word 1)) *)
  0x54fff861;       (* arm_BNE (word 2096908) *)
  0xd65f03c0        (* arm_RET X30 *)
];;
(*** BYTECODE END ***)

let MLDSA_USE_HINT_88_EXEC = ARM_MK_EXEC_RULE mldsa_poly_use_hint_88_mc;;


(* ========================================================================= *)
(* Functional specification: UseHint for ML-DSA parameter set 44             *)
(* GAMMA2 = (Q-1)/88 = 95232, 2*GAMMA2 = 190464, output range [0, 43]       *)
(* ========================================================================= *)

let mldsa_use_hint_88_spec = new_definition
  `mldsa_use_hint_88_spec (a:num) (h:num) =
   let a1_raw = ((((a + 127) DIV 128) * 11275 + 8388608) DIV 16777216) in
   let a1 = if a1_raw > 43 then 0 else a1_raw in
   let a0:int = &a - &a1 * &190464 in
   let a0' = if a0 > &4190208 then a0 - &8380417 else a0 in
   if h = 0 then a1
   else if a0' > &0 then if a1 = 43 then 0 else a1 + 1
   else if a1 = 0 then 43 else a1 - 1`;;

let mldsa_use_hint_88_asm = new_definition
  `mldsa_use_hint_88_asm (a:int32) (h:int32) : int32 =
   let a1 = word_ishr_round (word_2smulh a (word 1477838209)) 17 in
   let m:int32 = word_neg(word(bitval(word_igt a (word 8285184)))) in
   let a0 = word_add (word_sub a (word_mul a1 (word 190464))) m in
   let a1' = word_and a1 (word_not m) in
   let delta:int32 = word_or (word_neg(word(bitval(word_ile a0 (word 0))))) (word 1) in
   let tmp = word_add a1' (word_mul delta h) in
   let neg_mask:int32 = word_neg(word(bitval(word_igt tmp (word 43)))) in
   let tmp' = word_and tmp (word_not neg_mask) in
   word_umin tmp' (word 43)`;;

(* ========================================================================= *)
(* Helper lemmas                                                              *)
(* ========================================================================= *)

let IVAL_SMALL = MLDSA_IVAL_VAL;;
let VAL_IWORD_NUM = VAL_IWORD_NUM_32;;

let WORD_2SMULH_NOSATURATE_88 = prove(
  `!a:int32. val a < 8380417
   ==> word_2smulh a (word 1477838209:int32) : int32 =
       iword((&2 * &(val a) * &1477838209) div &2 pow 32)`,
  GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[word_2smulh; DIMINDEX_32] THEN
  ASM_SIMP_TAC[IVAL_SMALL] THEN
  CONV_TAC WORD_REDUCE_CONV THEN
  REWRITE_TAC[iword_saturate; word_INT_MIN; word_INT_MAX; DIMINDEX_32] THEN
  CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC WORD_REDUCE_CONV THEN
  CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV) THEN
  REWRITE_TAC[INT_OF_NUM_CLAUSES] THEN
  SIMP_TAC[INT_OF_NUM_DIV] THEN
  REWRITE_TAC[INT_POS_NEG_BOUND] THEN
  SUBGOAL_THEN `~(&((2 * val(a:int32) * 1477838209) DIV 4294967296):int > &2147483647)`
    (fun th -> REWRITE_TAC[th]) THEN
  REWRITE_TAC[INT_ARITH `~(x:int > y) <=> x <= y`; INT_OF_NUM_LE] THEN
  TRANS_TAC LE_TRANS `(2 * 8380416 * 1477838209) DIV 4294967296` THEN
  CONJ_TAC THENL
  [MATCH_MP_TAC DIV_MONO THEN ASM_ARITH_TAC;
   CONV_TAC NUM_REDUCE_CONV]);;

let VAL_DECOMPOSE_A1_88 = prove(
  `!a:int32. val a < 8380417
   ==> val(word_ishr_round (word_2smulh a (word 1477838209:int32)) 17 : int32)
       = ((2 * val a * 1477838209) DIV 4294967296 + 65536) DIV 131072`,
  GEN_TAC THEN DISCH_TAC THEN
  ASM_SIMP_TAC[WORD_2SMULH_NOSATURATE_88] THEN
  SUBGOAL_THEN `(2 * val(a:int32) * 1477838209) DIV 4294967296 < 2147483648`
    ASSUME_TAC THENL
  [TRANS_TAC LT_TRANS `(2 * 8380416 * 1477838209) DIV 4294967296 + 1` THEN
   CONJ_TAC THENL
   [MATCH_MP_TAC(ARITH_RULE `x <= y ==> x < y + 1`) THEN
    MATCH_MP_TAC DIV_MONO THEN ASM_ARITH_TAC; CONV_TAC NUM_REDUCE_CONV]; ALL_TAC] THEN
  REWRITE_TAC[INT_OF_NUM_CLAUSES] THEN SIMP_TAC[INT_OF_NUM_DIV] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  ABBREV_TAC `t:int32 = iword(&((2 * val(a:int32) * 1477838209) DIV 4294967296))` THEN
  SUBGOAL_THEN `val(t:int32) = (2 * val(a:int32) * 1477838209) DIV 4294967296`
    ASSUME_TAC THENL
  [EXPAND_TAC "t" THEN MATCH_MP_TAC VAL_IWORD_NUM THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `val(t:int32) < 2147483648` ASSUME_TAC THENL
  [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[word_ishr_round] THEN CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC INT_REDUCE_CONV THEN
  SUBGOAL_THEN `ival(t:int32) = &(val t)` ASSUME_TAC THENL
  [SIMP_TAC[ival; DIMINDEX_32] THEN CONV_TAC NUM_REDUCE_CONV THEN
   COND_CASES_TAC THEN ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[INT_OF_NUM_CLAUSES] THEN SIMP_TAC[INT_OF_NUM_DIV] THEN CONV_TAC NUM_REDUCE_CONV THEN
  SUBGOAL_THEN `(val(t:int32) + 65536) DIV 131072 < 2147483648` ASSUME_TAC THENL
  [ASM_REWRITE_TAC[] THEN
   TRANS_TAC LT_TRANS `(5767167 + 65536) DIV 131072 + 1` THEN CONJ_TAC THENL
   [MATCH_MP_TAC(ARITH_RULE `x <= y ==> x < y + 1`) THEN
    MATCH_MP_TAC DIV_MONO THEN ASM_ARITH_TAC; CONV_TAC NUM_REDUCE_CONV]; ALL_TAC] THEN
  ASM_SIMP_TAC[VAL_IWORD_NUM] THEN MATCH_MP_TAC VAL_IWORD_NUM THEN
  UNDISCH_THEN `val(t:int32) = (2 * val(a:int32) * 1477838209) DIV 4294967296`
    (SUBST1_TAC o SYM) THEN ASM_REWRITE_TAC[]);;

let WORD_IGT_THRESHOLD_88 = BITBLAST_RULE
  `!a:int32. val a < 8380417
    ==> word_igt a (word 8285184:int32) <=> val a > 8285184`;;

let A1_BOUND_88 = prove(
  `!a. a < 8380417
   ==> ((a + 127) DIV 128 * 11275 + 8388608) DIV 16777216 <= 44`,
  GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(SPEC `128` (SPEC `8380416 + 127` (SPEC `a + 127` DIV_MONO))) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  CONV_TAC NUM_REDUCE_CONV THEN DISCH_TAC THEN
  ABBREV_TAC `d = (a + 127) DIV 128` THEN
  MP_TAC(SPEC `16777216` (SPEC `751819508` (SPEC `d * 11275 + 8388608` DIV_MONO))) THEN
  ANTS_TAC THENL
  [SUBGOAL_THEN `d * 11275 <= 65472 * 11275` MP_TAC THENL
   [ASM_SIMP_TAC[LE_MULT_RCANCEL]; CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC];
   CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC]);;

let A1_BOUND_NOWRAP_88 = prove(
  `!a. a <= 8285184
   ==> ((a + 127) DIV 128 * 11275 + 8388608) DIV 16777216 <= 43`,
  GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(SPEC `128` (SPEC `8285184 + 127` (SPEC `a + 127` DIV_MONO))) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  CONV_TAC NUM_REDUCE_CONV THEN DISCH_TAC THEN
  ABBREV_TAC `d = (a + 127) DIV 128` THEN
  MP_TAC(SPEC `16777216` (SPEC `738196808` (SPEC `d * 11275 + 8388608` DIV_MONO))) THEN
  ANTS_TAC THENL
  [SUBGOAL_THEN `d * 11275 <= 64728 * 11275` MP_TAC THENL
   [ASM_SIMP_TAC[LE_MULT_RCANCEL]; CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC];
   CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC]);;

(* Barrett equivalence for _88: 45-interval case analysis *)
let DIV_SANDWICH = prove(
  `!x d k. ~(d = 0) /\ k * d <= x /\ x < (k + 1) * d ==> x DIV d = k`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `k <= x DIV d` ASSUME_TAC THENL
  [ASM_SIMP_TAC[LE_RDIV_EQ] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `x DIV d < k + 1` ASSUME_TAC THENL
  [ASM_SIMP_TAC[RDIV_LT_EQ] THEN ASM_ARITH_TAC; ASM_ARITH_TAC]);;

let BARRETT_INTERVAL_88 = prove(
  `!a lo hi k.
    lo <= a /\ a <= hi /\
    k * 131072 <= (2 * lo * 1477838209) DIV 4294967296 + 65536 /\
    (2 * hi * 1477838209) DIV 4294967296 + 65536 < (k + 1) * 131072 /\
    k * 16777216 <= (lo + 127) DIV 128 * 11275 + 8388608 /\
    (hi + 127) DIV 128 * 11275 + 8388608 < (k + 1) * 16777216
    ==> ((2 * a * 1477838209) DIV 4294967296 + 65536) DIV 131072 = k /\
        ((a + 127) DIV 128 * 11275 + 8388608) DIV 16777216 = k`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  CONJ_TAC THEN MATCH_MP_TAC DIV_SANDWICH THEN CONV_TAC NUM_REDUCE_CONV THENL
  [CONJ_TAC THENL
   [TRANS_TAC LE_TRANS `(2 * lo * 1477838209) DIV 4294967296 + 65536` THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[ARITH_RULE `x + 65536 <= y + 65536 <=> x <= y`] THEN
    MATCH_MP_TAC DIV_MONO THEN ASM_ARITH_TAC;
    TRANS_TAC LET_TRANS `(2 * hi * 1477838209) DIV 4294967296 + 65536` THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[ARITH_RULE `x + 65536 <= y + 65536 <=> x <= y`] THEN
    MATCH_MP_TAC DIV_MONO THEN ASM_ARITH_TAC];
   CONJ_TAC THENL
   [TRANS_TAC LE_TRANS `(lo + 127) DIV 128 * 11275 + 8388608` THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[ARITH_RULE `x + 8388608 <= y + 8388608 <=> x <= y`] THEN
    REWRITE_TAC[LE_MULT_RCANCEL] THEN DISJ1_TAC THEN
    MATCH_MP_TAC DIV_MONO THEN ASM_ARITH_TAC;
    TRANS_TAC LET_TRANS `(hi + 127) DIV 128 * 11275 + 8388608` THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[ARITH_RULE `x + 8388608 <= y + 8388608 <=> x <= y`] THEN
    REWRITE_TAC[LE_MULT_RCANCEL] THEN DISJ1_TAC THEN
    MATCH_MP_TAC DIV_MONO THEN ASM_ARITH_TAC]]);;

let BARRETT_EQUIV_88 = prove(
  `!a. a < 8380417 ==>
  ((2 * a * 1477838209) DIV 4294967296 + 65536) DIV 131072 =
  ((a + 127) DIV 128 * 11275 + 8388608) DIV 16777216`,
  GEN_TAC THEN DISCH_TAC THEN
  let intervals = [
    (0, 95232); (95233, 285696); (285697, 476160); (476161, 666624);
    (666625, 857088); (857089, 1047552); (1047553, 1238016);
    (1238017, 1428480); (1428481, 1618944); (1618945, 1809408);
    (1809409, 1999872); (1999873, 2190336); (2190337, 2380800);
    (2380801, 2571264); (2571265, 2761728); (2761729, 2952192);
    (2952193, 3142656); (3142657, 3333120); (3333121, 3523584);
    (3523585, 3714048); (3714049, 3904512); (3904513, 4094976);
    (4094977, 4285440); (4285441, 4475904); (4475905, 4666368);
    (4666369, 4856832); (4856833, 5047296); (5047297, 5237760);
    (5237761, 5428224); (5428225, 5618688); (5618689, 5809152);
    (5809153, 5999616); (5999617, 6190080); (6190081, 6380544);
    (6380545, 6571008); (6571009, 6761472); (6761473, 6951936);
    (6951937, 7142400); (7142401, 7332864); (7332865, 7523328);
    (7523329, 7713792); (7713793, 7904256); (7904257, 8094720);
    (8094721, 8285184); (8285185, 8380416)] in
  let mk_le hi =
    mk_comb(mk_comb(`(<=):num->num->bool`, mk_var("a",`:num`)),
            mk_small_numeral hi) in
  let apply_interval k (lo, hi) =
    let th = SPECL [`a:num`; mk_small_numeral lo;
                    mk_small_numeral hi; mk_small_numeral k]
                   BARRETT_INTERVAL_88 in
    MP_TAC th THEN CONV_TAC NUM_REDUCE_CONV THEN ASM_ARITH_TAC in
  let rec cascade k = function
    | [(lo,hi)] -> apply_interval k (lo,hi)
    | (lo,hi)::rest ->
        ASM_CASES_TAC (mk_le hi) THENL
        [apply_interval k (lo,hi); cascade (k+1) rest]
    | [] -> failwith "empty" in
  cascade 0 intervals);;



let WORD_SUB_SIGN_88 = BITBLAST_RULE
  `!a:int32 b:int32. val b <= 8189952 /\ val a <= 8285184 ==>
   ((bit 31 (word_sub a b) \/ word_sub a b = word 0) <=> val a <= val b)`;;

let WRAP_A0_NEGATIVE_88 = BITBLAST_RULE
  `!a:int32. val a < 8380417 /\ val a > 8285184
   ==> bit 31 (word_add (word_sub a (word 8380416:int32)) (word 4294967295:int32))`;;

let A1_WRAP_88 = prove(
  `!a. 8285184 < a /\ a < 8380417
   ==> ((a + 127) DIV 128 * 11275 + 8388608) DIV 16777216 = 44`,
  GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `44 <= ((a + 127) DIV 128 * 11275 + 8388608) DIV 16777216`
    ASSUME_TAC THENL
  [MP_TAC(SPEC `128` (SPEC `a + 127` (SPEC `8285185 + 127` DIV_MONO))) THEN
   ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
   CONV_TAC NUM_REDUCE_CONV THEN DISCH_TAC THEN
   ABBREV_TAC `d = (a + 127) DIV 128` THEN
   MP_TAC(SPEC `16777216` (SPEC `d * 11275 + 8388608` (SPEC `738208083` DIV_MONO))) THEN
   ANTS_TAC THENL
   [SUBGOAL_THEN `64729 * 11275 <= d * 11275` MP_TAC THENL
    [ASM_SIMP_TAC[LE_MULT_RCANCEL]; CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC];
    CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC]; ALL_TAC] THEN
  MP_TAC(SPEC `a:num` A1_BOUND_88) THEN ASM_REWRITE_TAC[] THEN
  DISCH_TAC THEN ASM_ARITH_TAC);;

let A0_UPPER_88 = prove(
  `!a. a <= 8285184
   ==> a < (((a + 127) DIV 128 * 11275 + 8388608) DIV 16777216 + 1) * 190464`,
  GEN_TAC THEN DISCH_TAC THEN
  ABBREV_TAC `nv = ((a + 127) DIV 128 * 11275 + 8388608) DIV 16777216` THEN
  SUBGOAL_THEN `nv * 16777216 <= (a + 127) DIV 128 * 11275 + 8388608` ASSUME_TAC THENL
  [EXPAND_TAC "nv" THEN MP_TAC(SPECL [`(a + 127) DIV 128 * 11275 + 8388608`; `16777216`] (CONJUNCT1 DIVISION_SIMP)) THEN ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(a + 127) DIV 128 <= 64728` ASSUME_TAC THENL
  [MP_TAC(SPEC `128` (SPEC `8285184 + 127` (SPEC `a + 127` DIV_MONO))) THEN ANTS_TAC THENL [ASM_ARITH_TAC; CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC]; ALL_TAC] THEN
  SUBGOAL_THEN `nv * 16777216 <= 64728 * 11275 + 8388608` ASSUME_TAC THENL
  [SUBGOAL_THEN `(a + 127) DIV 128 * 11275 <= 64728 * 11275` MP_TAC THENL [REWRITE_TAC[LE_MULT_RCANCEL] THEN DISJ1_TAC THEN ASM_ARITH_TAC; ASM_ARITH_TAC]; ALL_TAC] THEN
  SUBGOAL_THEN `nv <= 43` ASSUME_TAC THENL [CONV_TAC NUM_REDUCE_CONV THEN ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_ARITH_TAC);;

let WORD_IGT_43_BOUND = BITBLAST_RULE
  `!a:int32. val a <= 43 ==> ~(word_igt a (word 43:int32))`;;
let WORD_IGT_43_ADD1 = BITBLAST_RULE
  `!a:int32. val a <= 42 ==> ~(word_igt (word_add a (word 1:int32)) (word 43:int32))`;;
let WORD_IGT_43_SUB1 = BITBLAST_RULE
  `!a:int32. val a <= 43 /\ ~(val a = 0) ==>
   ~(word_igt (word_add a (word 4294967295:int32)) (word 43:int32))`;;
let WORD_IGT_43_TRUE = BITBLAST_RULE
  `word_igt (word 44:int32) (word 43:int32)`;;

let ELEMENT_CORRECT_88 = prove(
  `!a:int32 h:int32.
     val a < 8380417 /\ val h <= 1
     ==> val(mldsa_use_hint_88_asm a h) = mldsa_use_hint_88_spec (val a) (val h)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[mldsa_use_hint_88_asm; mldsa_use_hint_88_spec] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  ABBREV_TAC `nv = ((val(a:int32) + 127) DIV 128 * 11275 + 8388608) DIV 16777216` THEN
  SUBGOAL_THEN `val(word_ishr_round (word_2smulh (a:int32) (word 1477838209)) 17 : int32) = nv` ASSUME_TAC THENL
  [EXPAND_TAC "nv" THEN TRANS_TAC EQ_TRANS `((2 * val(a:int32) * 1477838209) DIV 4294967296 + 65536) DIV 131072` THEN CONJ_TAC THENL [MATCH_MP_TAC VAL_DECOMPOSE_A1_88 THEN ASM_REWRITE_TAC[]; MATCH_MP_TAC BARRETT_EQUIV_88 THEN ASM_REWRITE_TAC[]]; ALL_TAC] THEN
  SUBGOAL_THEN `nv <= 44` ASSUME_TAC THENL [MP_TAC(SPEC `val(a:int32)` A1_BOUND_88) THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `word_igt (a:int32) (word 8285184:int32) <=> val a > 8285184` SUBST1_TAC THENL [MP_TAC(SPEC `a:int32` WORD_IGT_THRESHOLD_88) THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_CASES_TAC `val(a:int32) > 8285184` THENL
  [(* Wrap case: val a > 8285184, nv = 44 *)
   REWRITE_TAC[ASSUME `val(a:int32) > 8285184`; bitval] THEN
   SUBGOAL_THEN `nv = 44` SUBST_ALL_TAC THENL [MP_TAC(SPEC `val(a:int32)` A1_WRAP_88) THEN ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
   ABBREV_TAC `a1w = word_ishr_round (word_2smulh (a:int32) (word 1477838209)) 17 : int32` THEN
   SUBGOAL_THEN `a1w = (word 44:int32)` SUBST_ALL_TAC THENL [EXPAND_TAC "a1w" THEN ONCE_REWRITE_TAC[GSYM WORD_VAL] THEN AP_TERM_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
   CONV_TAC WORD_REDUCE_CONV THEN
   CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC WORD_REDUCE_CONV THEN REWRITE_TAC[WORD_ILE_ZERO_32] THEN
   MP_TAC(SPEC `a:int32` WRAP_A0_NEGATIVE_88) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
   ASM_REWRITE_TAC[bitval] THEN CONV_TAC WORD_REDUCE_CONV THEN
   REWRITE_TAC[INT_MUL_LZERO; INT_SUB_RZERO] THEN
   SUBGOAL_THEN `~((if int_gt (&(val(a:int32))) (&4190208) then &(val a) - &8380417 else &(val a):int) > &0)` ASSUME_TAC THENL
   [REWRITE_TAC[INT_GT; INT_NOT_LT] THEN COND_CASES_TAC THENL
    [MP_TAC(REWRITE_RULE[GSYM INT_OF_NUM_LT] (ASSUME `val(a:int32) < 8380417`)) THEN INT_ARITH_TAC;
     POP_ASSUM(MP_TAC o REWRITE_RULE[INT_GT; INT_NOT_LT]) THEN
     MP_TAC(REWRITE_RULE[GSYM INT_OF_NUM_GT; INT_GT] (ASSUME `val(a:int32) > 8285184`)) THEN INT_ARITH_TAC]; ALL_TAC] THEN
   ASM_REWRITE_TAC[] THEN
   ASM_CASES_TAC `val(h:int32) = 0` THENL
   [REWRITE_TAC[ASSUME `val(h:int32) = 0`] THEN
    SUBGOAL_THEN `h:int32 = word 0` SUBST1_TAC THENL [REWRITE_TAC[GSYM VAL_EQ_0] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    CONV_TAC WORD_REDUCE_CONV THEN REWRITE_TAC[VAL_WORD_UMIN; VAL_WORD; DIMINDEX_32] THEN CONV_TAC NUM_REDUCE_CONV;
    REWRITE_TAC[ASSUME `~(val(h:int32) = 0)`] THEN
    SUBGOAL_THEN `h:int32 = word 1` SUBST1_TAC THENL [REWRITE_TAC[GSYM VAL_EQ_1] THEN ASM_ARITH_TAC; ALL_TAC] THEN
    CONV_TAC WORD_REDUCE_CONV THEN REWRITE_TAC[VAL_WORD_UMIN; VAL_WORD; DIMINDEX_32] THEN CONV_TAC NUM_REDUCE_CONV]
  ;(* Nowrap case: val a <= 8285184 *)
   REWRITE_TAC[ASSUME `~(val(a:int32) > 8285184)`; bitval] THEN
   SUBGOAL_THEN `nv <= 43` ASSUME_TAC THENL [MP_TAC(SPEC `val(a:int32)` A1_BOUND_NOWRAP_88) THEN ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
   SUBGOAL_THEN `(if nv > 43 then 0 else nv) = nv` SUBST1_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
   ABBREV_TAC `a1w = word_ishr_round (word_2smulh (a:int32) (word 1477838209)) 17 : int32` THEN
   SUBGOAL_THEN `a1w = (word nv:int32)` SUBST_ALL_TAC THENL [EXPAND_TAC "a1w" THEN GEN_REWRITE_TAC LAND_CONV [GSYM WORD_VAL] THEN AP_TERM_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
   CONV_TAC WORD_REDUCE_CONV THEN REWRITE_TAC[WORD_AND_REFL; WORD_ILE_ZERO_32; WORD_ADD_0; WORD_AND_ONES_32] THEN
   SUBGOAL_THEN `nv * 190464 <= 8189952` ASSUME_TAC THENL [SUBGOAL_THEN `nv * 190464 <= 43 * 190464` MP_TAC THENL [REWRITE_TAC[LE_MULT_RCANCEL] THEN DISJ1_TAC THEN ASM_ARITH_TAC; CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC]; ALL_TAC] THEN
   SUBGOAL_THEN `val(word_mul (word nv:int32) (word 190464:int32)) = nv * 190464` ASSUME_TAC THENL [REWRITE_TAC[VAL_WORD_MUL; VAL_WORD; DIMINDEX_32] THEN CONV_TAC NUM_REDUCE_CONV THEN SUBGOAL_THEN `nv MOD 4294967296 = nv` SUBST1_TAC THENL [MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC; ALL_TAC] THEN MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC; ALL_TAC] THEN
   SUBGOAL_THEN `val(word_mul (word nv:int32) (word 190464:int32)) <= 8189952` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
   SUBGOAL_THEN `(bit 31 (word_sub (a:int32) (word_mul (word nv:int32) (word 190464:int32))) \/ word_sub a (word_mul (word nv) (word 190464)) = word 0) <=> val a <= nv * 190464` SUBST1_TAC THENL
   [MP_TAC(ISPECL [`a:int32`; `word_mul (word nv:int32) (word 190464:int32)`] WORD_SUB_SIGN_88) THEN ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
   REWRITE_TAC[bitval] THEN
   SUBGOAL_THEN `val(word nv:int32) = nv` ASSUME_TAC THENL [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_32] THEN CONV_TAC NUM_REDUCE_CONV THEN ASM_ARITH_TAC; ALL_TAC] THEN
   SUBGOAL_THEN `~(word_igt (word nv:int32) (word 43:int32))` ASSUME_TAC THENL [MP_TAC(SPEC `word nv:int32` WORD_IGT_43_BOUND) THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
   ASM_CASES_TAC `val(h:int32) = 0` THENL
   [(* h = 0 nowrap *)
    REWRITE_TAC[ASSUME `val(h:int32) = 0`] THEN
    SUBGOAL_THEN `h:int32 = word 0` SUBST1_TAC THENL [REWRITE_TAC[GSYM VAL_EQ_0] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[WORD_MUL_0; WORD_ADD_0] THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC WORD_REDUCE_CONV THEN REWRITE_TAC[WORD_AND_ONES_32; VAL_WORD_UMIN; VAL_WORD; DIMINDEX_32] THEN CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `nv MOD 4294967296 = nv` SUBST1_TAC THENL [MATCH_MP_TAC MOD_LT THEN UNDISCH_TAC `nv <= 43` THEN ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[MIN] THEN UNDISCH_TAC `nv <= 43` THEN ARITH_TAC
   ;(* h = 1 nowrap *)
    REWRITE_TAC[ASSUME `~(val(h:int32) = 0)`] THEN
    SUBGOAL_THEN `h:int32 = word 1` SUBST1_TAC THENL [REWRITE_TAC[GSYM VAL_EQ_1] THEN ASM_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[WORD_MUL_1_32; WORD_AND_ONES_32] THEN
    SUBGOAL_THEN `val(word nv:int32) <= 43` ASSUME_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `~(int_gt (&(val(a:int32)) - &nv * &190464) (&4190208))` ASSUME_TAC THENL
    [REWRITE_TAC[INT_GT; INT_NOT_LT] THEN MP_TAC(SPEC `val(a:int32)` A0_UPPER_88) THEN ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN MP_TAC(REWRITE_RULE[GSYM INT_OF_NUM_LT; GSYM INT_OF_NUM_MUL; GSYM INT_OF_NUM_ADD] (ASSUME `val(a:int32) < (nv + 1) * 190464`)) THEN INT_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    ASM_CASES_TAC `val(a:int32) <= nv * 190464` THENL
    [MP_TAC(SPECL [`val(a:int32)`; `nv:num`; `190464`] REAL_INT_GT_BRIDGE) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[];
     MP_TAC(SPECL [`val(a:int32)`; `nv:num`; `190464`] REAL_INT_GT_BRIDGE_POS) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[]] THENL
    [(* delta = -1: a0' <= 0 *)
     REWRITE_TAC[bitval] THEN CONV_TAC WORD_REDUCE_CONV THEN REWRITE_TAC[WORD_AND_ONES_32] THEN
     ASM_CASES_TAC `nv = 0` THENL
     [ASM_REWRITE_TAC[] THEN CONV_TAC WORD_REDUCE_CONV THEN REWRITE_TAC[VAL_WORD_UMIN; VAL_WORD; DIMINDEX_32] THEN CONV_TAC NUM_REDUCE_CONV
     ;REWRITE_TAC[ASSUME `~(nv = 0)`] THEN
      SUBGOAL_THEN `~word_igt (word_add (word nv:int32) (word 4294967295)) (word 43:int32)` ASSUME_TAC THENL
      [MP_TAC(SPEC `word nv:int32` WORD_IGT_43_SUB1) THEN ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THENL [ASM_REWRITE_TAC[]; REWRITE_TAC[GSYM VAL_EQ_0] THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC]; ALL_TAC] THEN
      ASM_REWRITE_TAC[bitval] THEN CONV_TAC WORD_REDUCE_CONV THEN REWRITE_TAC[WORD_AND_ONES_32; VAL_WORD_UMIN; VAL_WORD_ADD; VAL_WORD; DIMINDEX_32] THEN CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `nv MOD 4294967296 = nv` SUBST1_TAC THENL [MATCH_MP_TAC MOD_LT THEN UNDISCH_TAC `nv <= 43` THEN ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `(nv + 4294967295) MOD 4294967296 = nv - 1` SUBST1_TAC THENL [SUBGOAL_THEN `nv + 4294967295 = (nv - 1) + 1 * 4294967296` SUBST1_TAC THENL [UNDISCH_TAC `~(nv = 0)` THEN ARITH_TAC; REWRITE_TAC[MOD_MULT_ADD] THEN MATCH_MP_TAC MOD_LT THEN UNDISCH_TAC `nv <= 43` THEN ARITH_TAC]; ALL_TAC] THEN
      REWRITE_TAC[MIN] THEN UNDISCH_TAC `nv <= 43` THEN ARITH_TAC]
    ;(* delta = +1: a0' > 0 *)
     REWRITE_TAC[bitval] THEN CONV_TAC WORD_REDUCE_CONV THEN REWRITE_TAC[WORD_AND_ONES_32] THEN
     ASM_CASES_TAC `nv = 43` THENL
     [ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC WORD_REDUCE_CONV THEN MP_TAC WORD_IGT_43_TRUE THEN DISCH_TAC THEN ASM_REWRITE_TAC[bitval] THEN CONV_TAC WORD_REDUCE_CONV THEN REWRITE_TAC[VAL_WORD_UMIN; VAL_WORD; DIMINDEX_32] THEN CONV_TAC NUM_REDUCE_CONV
     ;REWRITE_TAC[ASSUME `~(nv = 43)`] THEN
      SUBGOAL_THEN `~word_igt (word_add (word nv:int32) (word 1)) (word 43:int32)` ASSUME_TAC THENL
      [MP_TAC(SPEC `word nv:int32` WORD_IGT_43_ADD1) THEN ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN UNDISCH_TAC `nv <= 43` THEN UNDISCH_TAC `~(nv = 43)` THEN UNDISCH_TAC `val(word nv:int32) = nv` THEN ARITH_TAC; ALL_TAC] THEN
      ASM_REWRITE_TAC[bitval] THEN CONV_TAC WORD_REDUCE_CONV THEN REWRITE_TAC[WORD_AND_ONES_32; VAL_WORD_UMIN; VAL_WORD_ADD; VAL_WORD; DIMINDEX_32] THEN CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `nv MOD 4294967296 = nv` SUBST1_TAC THENL [MATCH_MP_TAC MOD_LT THEN UNDISCH_TAC `nv <= 43` THEN ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `(nv + 1) MOD 4294967296 = nv + 1` SUBST1_TAC THENL [MATCH_MP_TAC MOD_LT THEN UNDISCH_TAC `nv <= 43` THEN ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[MIN] THEN UNDISCH_TAC `nv <= 43` THEN UNDISCH_TAC `~(nv = 43)` THEN ARITH_TAC]]]]);;

let ELEMENT_CORRECT_WORD_88 = prove(
  `!a:int32 h:int32.
     val a < 8380417 /\ val h <= 1
     ==> mldsa_use_hint_88_asm a h =
         word(mldsa_use_hint_88_spec (val a) (val h))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  GEN_REWRITE_TAC LAND_CONV [GSYM WORD_VAL] THEN
  AP_TERM_TAC THEN MP_TAC(SPECL [`a:int32`; `h:int32`] ELEMENT_CORRECT_88) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> REWRITE_TAC[th]));;

(* ========================================================================= *)
(* Correctness proof with functional postcondition                           *)
(* ========================================================================= *)

let MLDSA_USE_HINT_88_CORRECT = prove
 (`!b a h x y pc.
    nonoverlapping (word pc, LENGTH mldsa_poly_use_hint_88_mc) (b, 1024) /\
    nonoverlapping (b, 1024) (a, 1024) /\
    nonoverlapping (b, 1024) (h, 1024)
    ==> ensures arm
          (\s. aligned_bytes_loaded s (word pc) mldsa_poly_use_hint_88_mc /\
               read PC s = word pc /\
               C_ARGUMENTS [b; a; h] s /\
               (!i. i < 256 ==> val(x i) < 8380417) /\
               (!i. i < 256 ==> val(y i) <= 1) /\
               (!i. i < 256 ==>
                 read(memory :> bytes32(word_add a (word(4 * i)))) s = x i) /\
               (!i. i < 256 ==>
                 read(memory :> bytes32(word_add h (word(4 * i)))) s = y i))
          (\s. read PC s = word(pc + 0x130) /\
               (!i. i < 256 ==>
                 read(memory :> bytes32(word_add b (word(4 * i)))) s =
                   word(mldsa_use_hint_88_spec (val(x i)) (val(y i)))))
          (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bytes(b, 1024)])`,

  MAP_EVERY X_GEN_TAC
    [`b:int64`; `a:int64`; `h:int64`;
     `x:num->int32`; `y:num->int32`; `pc:num`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              NONOVERLAPPING_CLAUSES; ALL;
              fst MLDSA_USE_HINT_88_EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  GLOBALIZE_PRECONDITION_TAC THEN
  CONV_TAC(RATOR_CONV(LAND_CONV(ONCE_DEPTH_CONV EXPAND_CASES_CONV))) THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[SOME_FLAGS; MODIFIABLE_SIMD_REGS] THEN

  ENSURES_INIT_TAC "s0" THEN
  MEMORY_128_FROM_32_TAC "a" 0 64 THEN
  ASM_REWRITE_TAC[WORD_ADD_0] THEN CONV_TAC WORD_REDUCE_CONV THEN
  STRIP_TAC THEN
  MEMORY_128_FROM_32_TAC "h" 0 64 THEN
  ASM_REWRITE_TAC[WORD_ADD_0] THEN CONV_TAC WORD_REDUCE_CONV THEN
  STRIP_TAC THEN
  DISCARD_MATCHING_ASSUMPTIONS [`read (memory :> bytes32 a) s = x`] THEN

  MAP_EVERY (fun n -> ARM_STEPS_TAC MLDSA_USE_HINT_88_EXEC [n] THEN
                      SIMD_SIMPLIFY_TAC[])
        (1--1006) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN

  REPEAT(FIRST_X_ASSUM(STRIP_ASSUME_TAC o
    CONV_RULE (SIMD_SIMPLIFY_CONV []) o
    CONV_RULE(READ_MEMORY_SPLIT_CONV 2) o
    check (can (term_match [] `read qqq s:int128 = xxx`) o concl))) THEN

  CONV_TAC(TOP_DEPTH_CONV EXPAND_CASES_CONV) THEN
  CONV_TAC(DEPTH_CONV NUM_MULT_CONV THENC DEPTH_CONV NUM_ADD_CONV) THEN
  REWRITE_TAC[WORD_ADD_0] THEN
  ASM_REWRITE_TAC[WORD_ADD_0] THEN ASM_REWRITE_TAC[] THEN

  (* Push word_subword through SIMD ops to per-element form *)
  REWRITE_TAC[WORD_SUBWORD_AND; WORD_SUBWORD_OR] THEN
  let WSN_TAC = REWRITE_TAC(map (fun n -> prove(
    subst [mk_small_numeral n, `n:num`]
      `!x:int128. word_subword(word_not x) (n,32):int32 = word_not(word_subword x (n,32))`,
    GEN_TAC THEN MATCH_MP_TAC WORD_SUBWORD_NOT THEN
    REWRITE_TAC[DIMINDEX_32; DIMINDEX_128] THEN ARITH_TAC)) [0;32;64;96]) in
  WSN_TAC THEN
  CONV_TAC(DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
  CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV) THEN
  let EC_DEEP = CONV_RULE(DEPTH_CONV WORD_NUM_RED_CONV)
    (CONV_RULE(DEPTH_CONV(INT_RED_CONV ORELSEC NUM_RED_CONV))
      (CONV_RULE(TOP_DEPTH_CONV let_CONV)
        (REWRITE_RULE[mldsa_use_hint_88_asm; word_2smulh; word_ishr_round;
                       DIMINDEX_32] ELEMENT_CORRECT_WORD_88))) in
  let EC_OR = ONCE_REWRITE_RULE[WORD_OR_SYM] EC_DEEP in
  REPEAT CONJ_TAC THEN
  (MATCH_MP_TAC EC_OR ORELSE MATCH_MP_TAC EC_DEEP) THEN
  CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ARITH_TAC);;

(* ========================================================================= *)
(* Subroutine form                                                           *)
(* ========================================================================= *)

let MLDSA_USE_HINT_88_SUBROUTINE_CORRECT = prove
 (`!b a h x y pc returnaddress.
    nonoverlapping (word pc, LENGTH mldsa_poly_use_hint_88_mc) (b, 1024) /\
    nonoverlapping (b, 1024) (a, 1024) /\
    nonoverlapping (b, 1024) (h, 1024)
    ==> ensures arm
          (\s. aligned_bytes_loaded s (word pc) mldsa_poly_use_hint_88_mc /\
               read PC s = word pc /\
               read X30 s = returnaddress /\
               C_ARGUMENTS [b; a; h] s /\
               (!i. i < 256 ==> val(x i) < 8380417) /\
               (!i. i < 256 ==> val(y i) <= 1) /\
               (!i. i < 256 ==>
                 read(memory :> bytes32(word_add a (word(4 * i)))) s = x i) /\
               (!i. i < 256 ==>
                 read(memory :> bytes32(word_add h (word(4 * i)))) s = y i))
          (\s. read PC s = returnaddress /\
               (!i. i < 256 ==>
                 read(memory :> bytes32(word_add b (word(4 * i)))) s =
                   word(mldsa_use_hint_88_spec (val(x i)) (val(y i)))))
          (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bytes(b, 1024)])`,
  REWRITE_TAC[fst MLDSA_USE_HINT_88_EXEC] THEN
  ARM_ADD_RETURN_NOSTACK_TAC MLDSA_USE_HINT_88_EXEC
    (REWRITE_RULE[fst MLDSA_USE_HINT_88_EXEC]
       MLDSA_USE_HINT_88_CORRECT));;

(* ========================================================================= *)
(* Constant-time and memory safety proof.                                    *)
(* ========================================================================= *)

needs "arm/proofs/consttime.ml";;
needs "arm/proofs/subroutine_signatures.ml";;


let full_spec,public_vars = mk_safety_spec
    ~keep_maychanges:false
    (assoc "mldsa_poly_use_hint_88" subroutine_signatures)
    MLDSA_USE_HINT_88_SUBROUTINE_CORRECT
    MLDSA_USE_HINT_88_EXEC;;

let MLDSA_USE_HINT_88_SUBROUTINE_SAFE = time prove
 (`exists f_events.
       forall e b a h pc returnaddress.
           nonoverlapping (word pc,LENGTH mldsa_poly_use_hint_88_mc) (b,1024) /\
           nonoverlapping (b,1024) (a,1024) /\
           nonoverlapping (b,1024) (h,1024)
           ==> ensures arm
               (\s.
                    aligned_bytes_loaded s (word pc)
                    mldsa_poly_use_hint_88_mc /\
                    read PC s = word pc /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [b; a; h] s /\
                    read events s = e)
               (\s.
                    read PC s = returnaddress /\
                    (exists e2.
                         read events s = APPEND e2 e /\
                         e2 = f_events a h b pc returnaddress /\
                         memaccess_inbounds e2 [a,1024; h,1024; b,1024]
                         [b,1024]))
               (\s s'. true)`,
  ASSERT_CONCL_TAC full_spec THEN
  PROVE_SAFETY_SPEC_TAC ~public_vars:public_vars MLDSA_USE_HINT_88_EXEC);;

