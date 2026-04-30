(* mono_preamble.ml — canonical replay to reach "loop body, after R9 bridge".

   Intended use: after `mcp__hol-light__hol_restart`, load this file to arrive
   at the live mid-proof state where:
     * Subgoal 1 (pre-loop init, pc → pc+104) is closed.
     * Subgoal 2 (loop body, pc+104 → {pc+104, pc+181}) has been entered with
       i quantifier stripped, curlist/curlen abbreviated, s0 initialized,
       JA resolutions done, verbose VSTEPS 22-29 applied, and the R9 popcount
       bridge established (read R9 s29 = word(LENGTH(FILTER …))).
     * Subgoal 3 (post-loop) is untouched.

   Two subgoals remain. Takes ~5 minutes.

   Extracted from mldsa_rej_uniform.ml lines 362-550 verbatim. *)

g `!res buf table (inlist:(24 word)list) pc stackpointer.
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
          MAYCHANGE [ZMM0; ZMM1; ZMM2; ZMM3; ZMM4] ,,
          MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
          MAYCHANGE [memory :> bytes(res,1024)])`;;

(* Phase 1: strip + WOP + ENSURES_WHILE_UP2 *)
e (MAP_EVERY X_GEN_TAC
   [`res:int64`; `buf:int64`; `table:int64`;
    `inlist:(24 word)list`; `pc:num`; `stackpointer:int64`] THEN
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS; NONOVERLAPPING_CLAUSES] THEN
  STRIP_TAC);;

e (SUBGOAL_THEN
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
    ALL_TAC]);;

e (ENSURES_WHILE_UP2_TAC `N:num` `pc + 104` `pc + 181`
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
  ASM_REWRITE_TAC[LT_REFL] THEN REPEAT CONJ_TAC);;

(* Now 3 subgoals: pre-loop, loop body, post-loop. Work on subgoal 1 (pre-loop). *)

(* Subgoal 1: pre-loop init (instrs 1-17) *)
e (ENSURES_INIT_TAC "s0" THEN
   X86_STEPS_TAC MLDSA_REJ_UNIFORM_EXEC (1--17) THEN
   ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
   CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
   REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES; SUB_LIST_CLAUSES; REJ_SAMPLE_EMPTY;
               LENGTH; num_of_wordlist] THEN
   CONV_TAC NUM_REDUCE_CONV THEN
   REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_MEMORY_BYTES_TRIVIAL] THEN
   CONV_TAC WORD_REDUCE_CONV);;

(* Subgoal 2: loop body setup *)
e (X_GEN_TAC `i:num` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `curlist = REJ_SAMPLE (SUB_LIST(0,8*i) inlist)` THEN
  ABBREV_TAC `curlen = LENGTH(curlist:int32 list)` THEN
  CONV_TAC(RATOR_CONV(LAND_CONV(TOP_DEPTH_CONV let_CONV))) THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(MP_TAC o C MATCH_MP (ASSUME `i:num < N`) o
    check (fun th -> is_forall(concl th))) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `curlen <= 248` ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `24 * i <= 808` ASSUME_TAC THENL
   [UNDISCH_TAC `24 * (i + 1) <= 832` THEN ARITH_TAC; ALL_TAC] THEN
  ENSURES_INIT_TAC "s0");;

(* JA resolutions *)
e (X86_STEPS_TAC MLDSA_REJ_UNIFORM_EXEC [18;19] THEN
  SUBGOAL_THEN `read RIP s19 = word(pc + 111):int64`
    (RESOLVE_JA_ONLY_TAC `s19:x86state`) THENL
   [RESOLVE_JA_CURLEN_TAC; ALL_TAC] THEN
  X86_STEPS_TAC MLDSA_REJ_UNIFORM_EXEC [20;21] THEN
  SUBGOAL_THEN `read RIP s21 = word(pc + 119):int64`
    (RESOLVE_JA_ONLY_TAC `s21:x86state`) THENL
   [RESOLVE_JA_OFFSET_TAC; ALL_TAC]);;

(* All-verbose SIMD + POPCNT pipeline *)
e (X86_VSTEPS_TAC MLDSA_REJ_UNIFORM_EXEC (22--29));;

(* R9 popcount bridge (mldsa_rej_uniform.ml:515-550 pattern, uses ASM_SIMP_TAC variant) *)
e (SUBGOAL_THEN
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
  MP_TAC);;

e (ASM_REWRITE_TAC[] THEN
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
  SIMP_TAC[WORD_ZX_ZX; DIMINDEX_32; DIMINDEX_64; ARITH_RULE `32 <= 64`] THEN
  SIMP_TAC[WORD_POPCOUNT_WORD_ZX; DIMINDEX_8; DIMINDEX_32; ARITH_RULE `8 <= 32`] THEN
  REWRITE_TAC[VMOVMSKPS_POPCOUNT_EQ; BIT_NESTED_JOIN_8] THEN
  REWRITE_TAC[POPCNT_VMOVMSKPS_LEMMA] THEN
  MATCH_MP_TAC MOD_LT THEN
  TRANS_TAC LTE_TRANS `9` THEN CONJ_TAC THENL
   [MATCH_MP_TAC(ARITH_RULE `n <= 8 ==> n < 9`) THEN
    W(MP_TAC o PART_MATCH lhand LENGTH_FILTER o lhand o snd) THEN
    REWRITE_TAC[LENGTH] THEN ARITH_TAC;
    ARITH_TAC]);;

(* Pull R9 antecedent into assumptions, drop the old MAYCHANGE-version *)
e (DISCARD_MATCHING_ASSUMPTIONS [`read R9 (s:x86state) = (x:int64)`] THEN
  STRIP_TAC);;

Printf.printf "=== PREAMBLE DONE: R9 bridge in scope ===\n%!";;
(* Apply the semantic bridge block + CMP_MASK bridge (mldsa_rej_uniform.ml:553-803). *)
let scrub_pred th =
  let c = concl th in
  not (can (find_term ((=) `YMM3`)) c &&
       can (find_term ((=) (mk_var("s26",`:x86state`)))) c) &&
  not (can (find_term ((=) `inlist:(24 word)list`)) c &&
       can (find_term (fun t ->
         try fst(dest_const t) = "num_of_wordlist" with _ -> false)) c &&
       can (find_term ((=) (mk_var("s21",`:x86state`)))) c) &&
  (can (find_term (fun t ->
      try let s = fst(dest_var t) in
          String.length s > 0 && String.get s 0 = Char.chr 115 && not (s = "stackpointer")
      with _ -> false)) c ||
   can (find_term ((=) `MAYCHANGE`)) c ||
   can (find_term ((=) `bytes_loaded`)) c);;

e (SUBGOAL_THEN
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
      REPEAT(FIRST_X_ASSUM(K ALL_TAC o check scrub_pred)) THEN
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
      REWRITE_TAC[GSYM(NUM_REDUCE_CONV `2 EXP 192`)] THEN
      ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `LENGTH(SUB_LIST(8*i,8) (inlist:(24 word)list)) = 8`
        ASSUME_TAC THENL
       [REWRITE_TAC[LENGTH_SUB_LIST] THEN
        CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN
        MATCH_MP_TAC(ARITH_RULE
          `8 * i + 8 <= l ==> MIN 8 (l - 8 * i) = 8`) THEN
        ASM_ARITH_TAC;
        ALL_TAC] THEN
      ASM_SIMP_TAC[CONV_RULE NUM_REDUCE_CONV MAP_REJ_COEFFS];
      ALL_TAC]);;

Printf.printf "=== bridge done ===\n%!";;
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
