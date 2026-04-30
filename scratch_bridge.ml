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
