(* Minimal defs — only things NOT in checkpoint *)

let R9_POPCNT_BRIDGE = prove
 (`!ymm3_26:int256.
   val(word_subword ymm3_26 (0,32):int32) < 8388608 /\
   val(word_subword ymm3_26 (32,32):int32) < 8388608 /\
   val(word_subword ymm3_26 (64,32):int32) < 8388608 /\
   val(word_subword ymm3_26 (96,32):int32) < 8388608 /\
   val(word_subword ymm3_26 (128,32):int32) < 8388608 /\
   val(word_subword ymm3_26 (160,32):int32) < 8388608 /\
   val(word_subword ymm3_26 (192,32):int32) < 8388608 /\
   val(word_subword ymm3_26 (224,32):int32) < 8388608
   ==> word(word_popcount
         (word_zx(word_zx(word
           (bitval(bit 31 (word_sub (word_subword ymm3_26 (0,32):int32) (word 8380417))) +
            2 * bitval(bit 31 (word_sub (word_subword ymm3_26 (32,32):int32) (word 8380417))) +
            4 * bitval(bit 31 (word_sub (word_subword ymm3_26 (64,32):int32) (word 8380417))) +
            8 * bitval(bit 31 (word_sub (word_subword ymm3_26 (96,32):int32) (word 8380417))) +
            16 * bitval(bit 31 (word_sub (word_subword ymm3_26 (128,32):int32) (word 8380417))) +
            32 * bitval(bit 31 (word_sub (word_subword ymm3_26 (160,32):int32) (word 8380417))) +
            64 * bitval(bit 31 (word_sub (word_subword ymm3_26 (192,32):int32) (word 8380417))) +
            128 * bitval(bit 31 (word_sub (word_subword ymm3_26 (224,32):int32) (word 8380417))))
          :byte):int32):int64)):int64 =
       word(LENGTH(FILTER (\c:int32. val c < 8380417)
         [word_subword ymm3_26 (0,32):int32;
          word_subword ymm3_26 (32,32);
          word_subword ymm3_26 (64,32);
          word_subword ymm3_26 (96,32);
          word_subword ymm3_26 (128,32);
          word_subword ymm3_26 (160,32);
          word_subword ymm3_26 (192,32);
          word_subword ymm3_26 (224,32)]))`,
  GEN_TAC THEN STRIP_TAC THEN AP_TERM_TAC THEN
  ASM_SIMP_TAC[SIGN_BIT_BITVAL] THEN
  MP_TAC(ISPECL
   [`word_subword (ymm3_26:int256) (0,32):int32`;
    `word_subword (ymm3_26:int256) (32,32):int32`;
    `word_subword (ymm3_26:int256) (64,32):int32`;
    `word_subword (ymm3_26:int256) (96,32):int32`;
    `word_subword (ymm3_26:int256) (128,32):int32`;
    `word_subword (ymm3_26:int256) (160,32):int32`;
    `word_subword (ymm3_26:int256) (192,32):int32`;
    `word_subword (ymm3_26:int256) (224,32):int32`]
   POPCNT_EQ_LENGTH_FILTER) THEN
  ASM_SIMP_TAC[SIGN_BIT_BITVAL] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  IMP_REWRITE_TAC[WORD_POPCOUNT_WORD_ZX] THEN
  REWRITE_TAC[DIMINDEX_8; DIMINDEX_32; DIMINDEX_64] THEN ARITH_TAC);;

(* JA branch resolution tactics from the proof file *)
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

Printf.printf "=== DEFS LOADED ===\n%!";;
