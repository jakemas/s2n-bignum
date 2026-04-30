(* Post-bridge work with 8 bounds saved — extends scratch_post_bridge.ml *)

e (FIRST_X_ASSUM(fun th ->
      if can (find_term (fun t -> try fst(dest_const t) = "FILTER" with _ -> false)) (concl th) &&
         can (find_term (fun t -> try fst(dest_const t) = "REJ_SAMPLE" with _ -> false)) (concl th) &&
         is_eq(concl th) &&
         not(can (find_term ((=) `LENGTH:(int32 list)->num`)) (concl th))
      then ASSUME_TAC th THEN ASSUME_TAC(AP_TERM `LENGTH:(int32 list)->num` th)
      else failwith "not filter_eq"));;

e (ABBREV_TAC `newlen = LENGTH(FILTER (\c:int32. val c < 8380417)
        [word_subword (read YMM3 s26:int256) (0,32):int32;
         word_subword (read YMM3 s26) (32,32);
         word_subword (read YMM3 s26) (64,32);
         word_subword (read YMM3 s26) (96,32);
         word_subword (read YMM3 s26) (128,32);
         word_subword (read YMM3 s26) (160,32);
         word_subword (read YMM3 s26) (192,32);
         word_subword (read YMM3 s26) (224,32)])`);;

e (SUBGOAL_THEN
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
     [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
        can (find_term (fun t -> try fst(dest_const t) = "FILTER" with _ -> false)) (concl th) &&
        can (find_term (fun t -> try fst(dest_const t) = "REJ_SAMPLE" with _ -> false)) (concl th) &&
        is_eq(concl th) &&
        not(can (find_term ((=) `LENGTH:(int32 list)->num`)) (concl th)))) THEN
      ASM_REWRITE_TAC[];
      ALL_TAC]);;

(* Save the 8 bounds BEFORE ABBREV-ing coeffs_ymm3.
   The YMM3 s29 assumption still has the raw word_and structure at this point. *)
e (SUBGOAL_THEN
   `val(word_subword (read YMM3 s29:int256) (0,32):int32) < 8388608 /\
    val(word_subword (read YMM3 s29:int256) (32,32):int32) < 8388608 /\
    val(word_subword (read YMM3 s29:int256) (64,32):int32) < 8388608 /\
    val(word_subword (read YMM3 s29:int256) (96,32):int32) < 8388608 /\
    val(word_subword (read YMM3 s29:int256) (128,32):int32) < 8388608 /\
    val(word_subword (read YMM3 s29:int256) (160,32):int32) < 8388608 /\
    val(word_subword (read YMM3 s29:int256) (192,32):int32) < 8388608 /\
    val(word_subword (read YMM3 s29:int256) (224,32):int32) < 8388608`
   STRIP_ASSUME_TAC THENL
    [(* Need: read YMM3 s29 = word_and (...) (...). Find it or derive it. *)
     (* We have `read YMM3 s22 = read (memory :> bytes256 ...)` (VMOVDQU).
        Then s22->s24 is VPERMQ (word_join permutation),
        s24->s25 is VPSHUFB,
        s25->s26 is VPAND with mask.
        Finally s26=s27=s28=s29 via the VPSUBD/VMOVMSKPS/POPCNT which don't touch YMM3.
        So the YMM3 s26 equation has word_and at top. Look for it. *)
     FIRST_ASSUM(fun th ->
       let c = concl th in
       if is_eq c &&
          (try fst(dest_const(fst(strip_comb(rhs c)))) = "word_and" with _ -> false) &&
          (try fst(dest_const(fst(strip_comb(lhs c)))) = "read" with _ -> false) &&
          (try fst(dest_const(rand(rator(lhs c)))) = "YMM3" with _ -> false)
       then SUBST1_TAC th
       else failwith "no YMM3 word_and") THEN
     REWRITE_TAC[WORD_SUBWORD_AND] THEN
     CONV_TAC(DEPTH_CONV(WORD_SIMPLE_SUBWORD_CONV ORELSEC WORD_NUM_RED_CONV)) THEN
     REPEAT CONJ_TAC THEN
     MATCH_MP_TAC(ARITH_RULE `n <= 8388607 ==> n < 8388608`) THEN
     REWRITE_TAC[VAL_WORD_AND_WORD_LE];
     ALL_TAC]);;

e (ABBREV_TAC `coeffs_ymm3:int256 = read YMM3 s29`);;
e (ABBREV_TAC `cmp_mask:int64 = read R8 s29`);;
e (ABBREV_TAC `table_entry:int64 =
      read (memory :> bytes64 (word_add table (word (8 * val (cmp_mask:int64))))) s29`);;

(* cmp_mask bridge *)
e (SUBGOAL_THEN
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
     [FIRST_ASSUM(fun h30 ->
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
      (* Use the preserved bounds directly — no more need for word_and structure *)
      ASM_REWRITE_TAC[];
      ALL_TAC]);;

Printf.printf "=== post-bridge v2 done — bounds and cmp_mask both in scope ===\n%!";;
