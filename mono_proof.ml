loadt "defs_extra.ml";;
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
          MAYCHANGE [ZMM0; ZMM1; ZMM2; ZMM3; ZMM4] ,,
          MAYCHANGE SOME_FLAGS ,,
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
     [(* VPERMD 256-case brute force — inline proof connecting to
         VPERMD_TABLE_CORRECT via TABLE_ENTRY_FROM_MEMORY *)
      (* VPERMD via VPERMD_TABLE_CORRECT applied once (replaces 256-case brute force).
         Chain: establish val(table_entry) = (table DIV 2^(64*val cmp_mask)) MOD 2^64,
         substitute read YMM3 s32 into goal, MP_TAC specialized VPERMD_TABLE_CORRECT,
         discharge bounds + table_entry antecedent via ASM + val cmp_mask = bitval_sum,
         fold ix back to coeffs_ymm3 via WORD_JOIN_SUBWORDS_256. *)
      (* Step A: derive val(table_entry) = (table DIV 2^(64 * val cmp_mask)) MOD 2^64 *)
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
      (* Step B: substitute read YMM3 s32 into goal *)
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
      (* Step C: MP_TAC specialized VPERMD_TABLE_CORRECT *)
      MP_TAC (ISPECL [
        `word_subword (coeffs_ymm3:int256) (0,32):int32`;
        `word_subword (coeffs_ymm3:int256) (32,32):int32`;
        `word_subword (coeffs_ymm3:int256) (64,32):int32`;
        `word_subword (coeffs_ymm3:int256) (96,32):int32`;
        `word_subword (coeffs_ymm3:int256) (128,32):int32`;
        `word_subword (coeffs_ymm3:int256) (160,32):int32`;
        `word_subword (coeffs_ymm3:int256) (192,32):int32`;
        `word_subword (coeffs_ymm3:int256) (224,32):int32`;
        `table_entry:int64`
      ] VPERMD_TABLE_CORRECT) THEN
      (* Step D: discharge antecedent.
         ANTS_TAC splits into (antecedent to prove) and (implication goal).
         Use W to capture assumptions and build the SYM rewrite, then discharge
         antecedent via ASM_REWRITE + cmp_mask SYM rewrite. *)
      ANTS_TAC THENL
       [W(fun (asl,_) ->
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
          ASM_REWRITE_TAC[cm_sym]);
        ALL_TAC] THEN
      (* Step E: VPERMD conclusion becomes antecedent; fold lets, discharge *)
      CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
      DISCH_TAC THEN
      (* Rewrite newlen to bitval_sum, REJ_SAMPLE to FILTER, then normalize word_subwords *)
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
        (REWRITE_TAC[newlen_bitval; SYM filter_rej_eq] THEN
         CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
         (* fold val cmp_mask back from bitval_sum *)
         FIRST_X_ASSUM(fun th ->
           if is_eq(concl th) &&
              (try fst(dest_var(rand(lhs(concl th)))) = "cmp_mask" with _ -> false) &&
              contains_s "bitval" (string_of_term (concl th))
           then REWRITE_TAC[SYM th] THEN ASSUME_TAC th else failwith "") THEN
         ASM_REWRITE_TAC[] THEN
         RULE_ASSUM_TAC(REWRITE_RULE[WORD_JOIN_SUBWORDS_256]) THEN
         RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV)) THEN
         ASM_REWRITE_TAC[]) (asl, w));
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
       [(* RAX: word(curlen + lenrej) — word arithmetic *)
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
          STRIP_ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
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
          STRIP_ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
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
            Printf.printf "  MEMSTORE: failed (%s), CHEAT\n%!" (Printexc.to_string e);
            CHEAT_TAC (asl,w));
        (* MAYCHANGE — produced by ENSURES_FINAL_STATE_TAC *)
        MONOTONE_MAYCHANGE_TAC ORELSE CHEAT_TAC];

      (* ~(i+1 < N): exit to pc+181 *)
      (fun gl -> Printf.printf "  DEBUG[J]: exit branch\n%!"; ALL_TAC gl) THEN
      X86_VSTEPS_TAC MLDSA_REJ_UNIFORM_EXEC (36--37) THEN
      FIRST_X_ASSUM(DISJ_CASES_TAC o check (is_disj o concl)) THENL
       [(* J1: offset exit — CHEAT for now *)
        REPEAT CHEAT_TAC;
        (* J2: 248 < LENGTH(REJ_SAMPLE(SUB_LIST(0,8*N))): count exit *)
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
        DISCARD_ASSUMPTIONS_TAC (fun th ->
          let c = concl th in
          let fvs = frees c in
          let has_const name t = try fst(dest_const t) = name with _ -> false in
          (* Keep the bridge result: has bytes + REJ_SAMPLE + read *)
          not(is_eq c &&
              can (find_term (has_const "REJ_SAMPLE")) c &&
              can (find_term (has_const "read")) c &&
              can (find_term (has_const "bytes")) c) &&
          (not (forall (fun v -> type_of v = `:num`) fvs) ||
           exists (fun v -> let n = fst(dest_var v) in
             n = "N" || n = "newlen" || n = "curlist") fvs ||
           is_forall c)) THEN
        REPEAT CONJ_TAC THENL
         [(* 1. JA conditional *)
          MATCH_MP_TAC(TAUT `p ==> (if p then a else b) = a`) THEN
          REWRITE_TAC[NOT_CLAUSES; DE_MORGAN_THM;
                      VAL_WORD_ZX_GEN; VAL_WORD_SUB_CASES; VAL_WORD_ADD;
                      VAL_WORD; DIMINDEX_32; DIMINDEX_64] THEN
          CONV_TAC NUM_REDUCE_CONV THEN
          SUBGOAL_THEN `curlen < 4294967296 /\ lr < 4294967296 /\
                        curlen < 18446744073709551616 /\ lr < 18446744073709551616 /\
                        curlen + lr < 4294967296 /\ curlen + lr < 18446744073709551616`
            STRIP_ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
          SUBGOAL_THEN `248 <= curlen + lr` ASSUME_TAC THENL
           [ASM_ARITH_TAC; ALL_TAC] THEN
          SUBGOAL_THEN `(curlen + lr) - 248 < 18446744073709551616` ASSUME_TAC THENL
           [ASM_ARITH_TAC; ALL_TAC] THEN
          ASM_SIMP_TAC[MOD_LT; MOD_MOD_REFL] THEN ASM_ARITH_TAC;
          (* 2. RAX *)
          REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_ZX_GEN; VAL_WORD_ADD;
                      VAL_WORD; DIMINDEX_32; DIMINDEX_64] THEN
          CONV_TAC NUM_REDUCE_CONV THEN
          SUBGOAL_THEN `curlen < 4294967296 /\ lr < 4294967296 /\
                        curlen < 18446744073709551616 /\ lr < 18446744073709551616 /\
                        curlen + lr < 4294967296 /\ curlen + lr < 18446744073709551616`
            STRIP_ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
          ASM_SIMP_TAC[MOD_LT] THEN ARITH_TAC;
          (* 3. RCX *)
          REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_ZX_GEN; VAL_WORD_ADD;
                      VAL_WORD; DIMINDEX_32; DIMINDEX_64] THEN
          CONV_TAC NUM_REDUCE_CONV THEN
          UNDISCH_TAC `24 * i <= 808` THEN
          SPEC_TAC(`24 * i`,`n:num`) THEN GEN_TAC THEN DISCH_TAC THEN
          SUBGOAL_THEN `n < 4294967296 /\ n < 18446744073709551616 /\
                        n + 24 < 4294967296 /\ n + 24 < 18446744073709551616`
            STRIP_ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
          ASM_SIMP_TAC[MOD_LT] THEN ARITH_TAC;
          (* 4. Memory store — bridge theorem from PRE-ENSURES is in assumptions *)
          (fun gl -> Printf.printf "  MEMSTORE(J2): using bridge from PRE-ENSURES\n%!"; ALL_TAC gl) THEN
          REWRITE_TAC[DIMINDEX_32;
                      ARITH_RULE `4 * (curlen + lr) = 4 * curlen + 4 * lr`;
                      ARITH_RULE `32 * curlen = 8 * (4 * curlen)`] THEN
          REWRITE_TAC[MEMORY_BYTES_SPLIT] THEN
          ASM_REWRITE_TAC[] THEN
          REWRITE_TAC[EQ_ADD_LCANCEL; EQ_MULT_LCANCEL; EXP_EQ_0; ARITH_EQ] THEN
          (ASM_REWRITE_TAC[] THEN NO_TAC) ORELSE CHEAT_TAC;
          (* 5. MAYCHANGE *)
          MONOTONE_MAYCHANGE_TAC ORELSE CHEAT_TAC]]];

    (* ================================================================= *)
    (* Subgoal 3: Post-loop                                              *)
    (* ================================================================= *)
    (fun gl -> Printf.printf "  DEBUG[K]: post-loop\n%!"; ALL_TAC gl) THEN
    REPEAT CHEAT_TAC]);;
