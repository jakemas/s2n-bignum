(* Test the exact tactic structure from mldsa_rej_uniform.ml replacement block,
   but as a single e(...) call. If this works, the monolithic should work too. *)

e (DISCARD_OLDSTATE_TAC "s29" THEN CLARIFY_TAC THEN
   X86_VSTEPS_TAC MLDSA_REJ_UNIFORM_EXEC (30--32) THEN
   SUBGOAL_THEN
      `val(read YMM3 s32:int256) MOD 2 EXP (32 * newlen) =
       num_of_wordlist(REJ_SAMPLE(SUB_LIST(8*i,8) (inlist:(24 word)list)))`
      ASSUME_TAC THENL
     [
      (* Step A *)
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
      (* Step B *)
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
      (* Step C: MP_TAC VPERMD_TABLE_CORRECT *)
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
      (* Step D: discharge antecedent *)
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
      (* Step E: reduce lets, DISCH, rewrite *)
      CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
      DISCH_TAC THEN
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
         FIRST_X_ASSUM(fun th ->
           if is_eq(concl th) &&
              (try fst(dest_var(rand(lhs(concl th)))) = "cmp_mask" with _ -> false) &&
              contains_s "bitval" (string_of_term (concl th))
           then REWRITE_TAC[SYM th] THEN ASSUME_TAC th else failwith "") THEN
         ASM_REWRITE_TAC[] THEN
         RULE_ASSUM_TAC(REWRITE_RULE[WORD_JOIN_SUBWORDS_256]) THEN
         RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV)) THEN
         ASM_REWRITE_TAC[]) (asl, w));
      ALL_TAC]);;

Printf.printf "=== VPERMD mono-form test done ===\n%!";;
