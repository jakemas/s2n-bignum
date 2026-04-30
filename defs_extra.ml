(* Lemmas that defs.ml / step*.ml need but which weren't in the checkpoint loader.
   Extracted verbatim from mldsa_rej_uniform.ml. Load before defs.ml. *)

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

(* word_join of 8 consecutive 32-bit subwords reconstructs the original 256-bit word.
   Used by the VPERMD bridge to fold the VPERMD expression back to coeffs_ymm3. *)
let WORD_JOIN_SUBWORDS_256 = prove
 (`!q:int256.
    word_join
     (word_join (word_join ((word_subword q (224,32)):int32) ((word_subword q (192,32)):int32):int64)
                (word_join ((word_subword q (160,32)):int32) ((word_subword q (128,32)):int32):int64):int128)
     (word_join (word_join ((word_subword q (96,32)):int32) ((word_subword q (64,32)):int32):int64)
                (word_join ((word_subword q (32,32)):int32) ((word_subword q (0,32)):int32):int64):int128):int256 = q`,
  GEN_TAC THEN CONV_TAC WORD_BLAST);;

(* Standalone VPERMD bridge: given 8 bounds on subwords of q and the table lookup
   value of te, the VPERMD expansion of (q, te) mod 2^(32*popcount) equals
   num_of_wordlist(FILTER (val<Q) [subwords]).
   Packages VPERMD_TABLE_CORRECT + WORD_JOIN_SUBWORDS_256 into one MP_TAC-able form
   that eliminates the 256-case brute force (255 CHEATs) in the main proof. *)
let MLDSA_VPERMD_BRIDGE = prove
 (`!(q:int256) (te:int64).
     val(word_subword q (0,32):int32) < 8388608 /\
     val(word_subword q (32,32):int32) < 8388608 /\
     val(word_subword q (64,32):int32) < 8388608 /\
     val(word_subword q (96,32):int32) < 8388608 /\
     val(word_subword q (128,32):int32) < 8388608 /\
     val(word_subword q (160,32):int32) < 8388608 /\
     val(word_subword q (192,32):int32) < 8388608 /\
     val(word_subword q (224,32):int32) < 8388608 /\
     val te = (num_of_wordlist mldsa_rej_uniform_table DIV
       2 EXP (64 * (bitval(val(word_subword q (0,32):int32) < 8380417) +
                    2 * bitval(val(word_subword q (32,32):int32) < 8380417) +
                    4 * bitval(val(word_subword q (64,32):int32) < 8380417) +
                    8 * bitval(val(word_subword q (96,32):int32) < 8380417) +
                    16 * bitval(val(word_subword q (128,32):int32) < 8380417) +
                    32 * bitval(val(word_subword q (160,32):int32) < 8380417) +
                    64 * bitval(val(word_subword q (192,32):int32) < 8380417) +
                    128 * bitval(val(word_subword q (224,32):int32) < 8380417))))
       MOD 2 EXP 64
     ==>
     val(word_join
           (word_join
             (word_join ((word_subword q (32 * val(word_subword te (56,3):3 word), 32)):int32)
                        ((word_subword q (32 * val(word_subword te (48,3):3 word), 32)):int32):int64)
             (word_join ((word_subword q (32 * val(word_subword te (40,3):3 word), 32)):int32)
                        ((word_subword q (32 * val(word_subword te (32,3):3 word), 32)):int32):int64):int128)
           (word_join
             (word_join ((word_subword q (32 * val(word_subword te (24,3):3 word), 32)):int32)
                        ((word_subword q (32 * val(word_subword te (16,3):3 word), 32)):int32):int64)
             (word_join ((word_subword q (32 * val(word_subword te (8,3):3 word), 32)):int32)
                        ((word_subword q (32 * val(word_subword te (0,3):3 word), 32)):int32):int64):int128):int256) MOD
     2 EXP (32 * (bitval(val(word_subword q (0,32):int32) < 8380417) +
                  bitval(val(word_subword q (32,32):int32) < 8380417) +
                  bitval(val(word_subword q (64,32):int32) < 8380417) +
                  bitval(val(word_subword q (96,32):int32) < 8380417) +
                  bitval(val(word_subword q (128,32):int32) < 8380417) +
                  bitval(val(word_subword q (160,32):int32) < 8380417) +
                  bitval(val(word_subword q (192,32):int32) < 8380417) +
                  bitval(val(word_subword q (224,32):int32) < 8380417))) =
     num_of_wordlist(FILTER (\c:int32. val c < 8380417)
       [word_subword q (0,32); word_subword q (32,32);
        word_subword q (64,32); word_subword q (96,32);
        word_subword q (128,32); word_subword q (160,32);
        word_subword q (192,32); word_subword q (224,32)])`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [
    `word_subword (q:int256) (0,32):int32`;
    `word_subword (q:int256) (32,32):int32`;
    `word_subword (q:int256) (64,32):int32`;
    `word_subword (q:int256) (96,32):int32`;
    `word_subword (q:int256) (128,32):int32`;
    `word_subword (q:int256) (160,32):int32`;
    `word_subword (q:int256) (192,32):int32`;
    `word_subword (q:int256) (224,32):int32`;
    `te:int64`
  ] VPERMD_TABLE_CORRECT) THEN
  ASM_REWRITE_TAC[] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[WORD_JOIN_SUBWORDS_256] THEN
  CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
  DISCH_THEN ACCEPT_TAC);;

(* ------------------------------------------------------------------------- *)
(* REJ_SAMPLE list decomposition helpers for the post-loop proof.            *)
(* ------------------------------------------------------------------------- *)

(* REJ_SAMPLE of a list is APPEND of REJ_SAMPLE of a prefix and a suffix. *)
let REJ_SAMPLE_SPLIT = prove
 (`!(l:(24 word)list) n.
    REJ_SAMPLE l = APPEND (REJ_SAMPLE (SUB_LIST (0,n) l))
                          (REJ_SAMPLE (SUB_LIST (n, LENGTH l - n) l))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[GSYM REJ_SAMPLE_APPEND] THEN
  MESON_TAC[SUB_LIST_TOPSPLIT]);;

(* If a prefix's REJ_SAMPLE has length 256, then the first 256 of REJ_SAMPLE
   of the full list equals REJ_SAMPLE of that prefix. Used in the post-loop
   JAE-exit case to conclude outlist = SUB_LIST (0,256) (REJ_SAMPLE inlist). *)
let REJ_SAMPLE_PREFIX_256 = prove
 (`!(inlist:(24 word)list) k.
    LENGTH (REJ_SAMPLE (SUB_LIST (0,k) inlist)) = 256
    ==> SUB_LIST (0,256) (REJ_SAMPLE inlist) = REJ_SAMPLE (SUB_LIST (0,k) inlist)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`inlist:(24 word)list`; `k:num`] REJ_SAMPLE_SPLIT) THEN
  DISCH_THEN(fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [th]) THEN
  MP_TAC(ISPECL
   [`REJ_SAMPLE (SUB_LIST (0,k) (inlist:(24 word)list))`;
    `REJ_SAMPLE (SUB_LIST (k, LENGTH inlist - k) (inlist:(24 word)list))`;
    `256`] SUB_LIST_APPEND_LEFT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[LE_REFL]; ALL_TAC] THEN
  DISCH_THEN SUBST1_TAC THEN
  MATCH_MP_TAC SUB_LIST_REFL THEN
  ASM_REWRITE_TAC[LE_REFL]);;

Printf.printf "=== defs_extra loaded ===\n%!";;
