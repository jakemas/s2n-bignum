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
          MAYCHANGE SOME_FLAGS ,,
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
