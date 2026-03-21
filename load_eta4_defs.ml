(* Load remaining definitions and lemmas for eta4 proof *)

let pair_wordlist = define
 `(!hi (lo:N word) rest.
     pair_wordlist (CONS lo (CONS hi rest)) =
     CONS (word_join hi lo:((N)tybit0)word) (pair_wordlist rest)) /\
  (!w. pair_wordlist [w] = [word_join (word 0:N word) w]) /\
  pair_wordlist [] = []`;;

let NUM_OF_PAIR_WORDLIST = prove
 (`!l:(N word)list. num_of_wordlist (pair_wordlist l) = num_of_wordlist l`,
  GEN_TAC THEN WF_INDUCT_TAC `LENGTH(l:(N word)list)` THEN
  POP_ASSUM MP_TAC THEN SPEC_TAC(`l:(N word)list`,`l:(N word)list`) THEN
  MATCH_MP_TAC list_INDUCT THEN
  REWRITE_TAC[pair_wordlist; num_of_wordlist] THEN
  MAP_EVERY X_GEN_TAC [`lo:N word`; `med:(N word)list`] THEN
  DISCH_THEN(K ALL_TAC) THEN
  SPEC_TAC(`med:(N word)list`,`med:(N word)list`) THEN
  MATCH_MP_TAC list_INDUCT THEN
  REWRITE_TAC[pair_wordlist; num_of_wordlist] THEN
  SIMP_TAC[MULT_CLAUSES; ADD_CLAUSES; VAL_WORD_JOIN_SIMPLE; DIMINDEX_TYBIT0;
           VAL_WORD_0; GSYM MULT_2; LENGTH; ARITH_RULE `n < SUC(SUC n)`] THEN
  REWRITE_TAC[MULT_2; EXP_ADD] THEN ARITH_TAC);;

let NUM_OF_WORDLIST_SING = prove
 (`!h:N word. num_of_wordlist [h] = val h`,
  REWRITE_TAC[num_of_wordlist; MULT_CLAUSES; ADD_CLAUSES]);;

let NUM_OF_WORDLIST_APPEND = prove
 (`!lis1 lis2:(N word)list.
        num_of_wordlist(APPEND lis1 lis2) =
        num_of_wordlist lis1 +
        2 EXP (dimindex(:N) * LENGTH lis1) * num_of_wordlist lis2`,
  LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[APPEND; LENGTH; num_of_wordlist] THEN
  ASM_REWRITE_TAC[MULT_CLAUSES; EXP; ADD_CLAUSES] THEN
  REWRITE_TAC[EXP_ADD] THEN ARITH_TAC);;

let NUM_OF_WORDLIST_BOUND_LENGTH = prove
 (`!l:(N word)list. num_of_wordlist l < 2 EXP (dimindex(:N) * LENGTH l)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[LENGTH; num_of_wordlist] THEN
  REWRITE_TAC[MULT_CLAUSES; EXP; EXP_ADD; ARITH] THEN
  W(MP_TAC o PART_MATCH lhand VAL_BOUND o lhand o lhand o snd) THEN
  MATCH_MP_TAC(ARITH_RULE
   `n * (x + 1) <= y ==> h < n ==> h + n * x < y`) THEN
  ASM_REWRITE_TAC[LE_MULT_LCANCEL] THEN ASM_ARITH_TAC);;

let NUM_OF_WORDLIST_BOUND = prove
 (`!l:(N word)list n.
        LENGTH l <= n ==> num_of_wordlist l < 2 EXP (dimindex(:N) * n)`,
  REPEAT STRIP_TAC THEN
  TRANS_TAC LTE_TRANS `2 EXP (dimindex(:N) * LENGTH(l:(N word)list))` THEN
  ASM_REWRITE_TAC[NUM_OF_WORDLIST_BOUND_LENGTH; LE_EXP; LE_MULT_LCANCEL] THEN
  ASM_ARITH_TAC);;

let NUM_OF_WORDLIST_SUB_LIST_0 = prove
 (`!(l:(N word)list) n.
        num_of_wordlist(SUB_LIST(0,n) l) =
        num_of_wordlist l MOD 2 EXP (dimindex(:N) * n)`,
  MATCH_MP_TAC list_INDUCT THEN
  REWRITE_TAC[SUB_LIST_CLAUSES; num_of_wordlist; DIV_0; MOD_0] THEN
  MAP_EVERY X_GEN_TAC [`h:N word`; `t:(N word)list`] THEN
  DISCH_TAC THEN MATCH_MP_TAC num_INDUCTION THEN
  ASM_REWRITE_TAC[SUB_LIST_CLAUSES; num_of_wordlist] THEN
  REWRITE_TAC[MULT_CLAUSES; EXP; MOD_1] THEN
  X_GEN_TAC `n:num` THEN DISCH_THEN(K ALL_TAC) THEN
  CONV_TAC SYM_CONV THEN REWRITE_TAC[MOD_UNIQUE] THEN
  REWRITE_TAC[EXP_ADD] THEN CONJ_TAC THENL
   [DISJ2_TAC THEN MATCH_MP_TAC(ARITH_RULE
     `h < n /\ n * (t + 1) <= n * e
      ==> h + n * t < n * e`) THEN
    REWRITE_TAC[VAL_BOUND; LE_MULT_LCANCEL] THEN DISJ2_TAC THEN
    REWRITE_TAC[ARITH_RULE `n + 1 <= m <=> n < m`; MOD_LT_EQ] THEN
    REWRITE_TAC[EXP_EQ_0; ARITH_EQ];
    MATCH_MP_TAC(NUMBER_RULE
     `(t == t') (mod d)
      ==> (h + e * t == h + e * t') (mod (e * d))`) THEN
    REWRITE_TAC[CONG_RMOD; CONG_REFL]]);;

let NUM_OF_WORDLIST_SUB_LIST = prove
 (`!(l:(N word)list) m n.
        num_of_wordlist (SUB_LIST(m,n) l) =
        (num_of_wordlist l DIV 2 EXP (dimindex(:N) * m)) MOD
        2 EXP (dimindex(:N) * n)`,
  MATCH_MP_TAC list_INDUCT THEN
  REWRITE_TAC[SUB_LIST_CLAUSES; num_of_wordlist; DIV_0; MOD_0] THEN
  MAP_EVERY X_GEN_TAC [`h:N word`; `t:(N word)list`] THEN
  DISCH_TAC THEN MATCH_MP_TAC num_INDUCTION THEN
  REWRITE_TAC[NUM_OF_WORDLIST_SUB_LIST_0; GSYM(CONJUNCT2 num_of_wordlist);
              EXP; DIV_1; MULT_CLAUSES] THEN
  ASM_REWRITE_TAC[SUB_LIST_CLAUSES; num_of_wordlist] THEN
  X_GEN_TAC `m:num` THEN DISCH_THEN(K ALL_TAC) THEN X_GEN_TAC `n:num` THEN
  SIMP_TAC[EXP_ADD; GSYM DIV_DIV; DIV_MULT_ADD; EXP_EQ_0; ARITH_EQ] THEN
  SIMP_TAC[DIV_LT; VAL_BOUND; ADD_CLAUSES]);;

let SUB_LIST_REFL = prove
 (`!(l:A list) n. LENGTH l <= n ==> SUB_LIST(0,n) l = l`,
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[SUB_LIST_CLAUSES] THEN
  INDUCT_TAC THEN ASM_SIMP_TAC[SUB_LIST_CLAUSES; LE_SUC; LENGTH] THEN
  ARITH_TAC);;

let NUM_OF_WORDLIST_EL = prove
 (`!(l:(N word)list) m.
        (num_of_wordlist l DIV 2 EXP (dimindex(:N) * m)) MOD
        2 EXP (dimindex(:N)) =
        if m < LENGTH l then val(EL m l) else 0`,
  REPEAT GEN_TAC THEN
  MP_TAC(SPECL [`l:(N word)list`; `m:num`; `1`]
   NUM_OF_WORDLIST_SUB_LIST) THEN
  REWRITE_TAC[MULT_CLAUSES] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[SUB_LIST_1] THEN COND_CASES_TAC THEN
  REWRITE_TAC[NUM_OF_WORDLIST_SING; num_of_wordlist]);;

let SUB_LIST_1 = prove
 (`!(l:A list) n. SUB_LIST(n,1) l = if n < LENGTH l then [EL n l] else []`,
  MATCH_MP_TAC list_INDUCT THEN
  REWRITE_TAC[LENGTH; CONJUNCT1 LT; SUB_LIST_CLAUSES] THEN
  MAP_EVERY X_GEN_TAC [`h:A`; `t:A list`] THEN DISCH_TAC THEN
  MATCH_MP_TAC num_INDUCTION THEN
  REWRITE_TAC[SUB_LIST_CLAUSES; LT_0; num_CONV `1`; EL; TL] THEN
  ASM_REWRITE_TAC[GSYM(num_CONV `1`); LT_SUC; HD]);;

let LENGTH_FILTER = prove
 (`!P l:A list. LENGTH(FILTER P l) <= LENGTH l`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[FILTER; LE_REFL] THEN
  COND_CASES_TAC THEN REWRITE_TAC[LENGTH] THEN ASM_ARITH_TAC);;

let SUB_LIST_APPEND_LEFT = prove
 (`!(l:A list) m n.
        n <= LENGTH l ==> SUB_LIST(0,n) (APPEND l m) = SUB_LIST(0,n) l`,
  LIST_INDUCT_TAC THEN
  SIMP_TAC[LENGTH; CONJUNCT1 LE; SUB_LIST_CLAUSES] THEN
  ONCE_REWRITE_TAC[SWAP_FORALL_THM] THEN
  INDUCT_TAC THEN ASM_SIMP_TAC[SUB_LIST_CLAUSES; APPEND; LE_SUC]);;

let NIBBLES = define
 `NIBBLES ([] : byte list) : byte list = [] /\
  NIBBLES (CONS b rest) =
    CONS (word(val b MOD 16) : byte)
         (CONS (word(val b DIV 16) : byte) (NIBBLES rest))`;;

let NIBBLES_APPEND = prove
 (`!l1 l2 : byte list.
    NIBBLES(APPEND l1 l2) = APPEND (NIBBLES l1) (NIBBLES l2)`,
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[NIBBLES; APPEND]);;

let LENGTH_NIBBLES = prove
 (`!l : byte list. LENGTH(NIBBLES l) = 2 * LENGTH l`,
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[NIBBLES; LENGTH] THEN ARITH_TAC);;

let SCRATCH_ETA4 = define
 `SCRATCH_ETA4 l = MAP (\x. word(val x):(16)word) (FILTER (\x:byte. val x < 9) (NIBBLES l))`;;

let SCRATCH_ETA4_EMPTY = prove
 (`SCRATCH_ETA4 [] = []`,
  REWRITE_TAC[SCRATCH_ETA4; NIBBLES; FILTER; MAP]);;

let SCRATCH_ETA4_APPEND = prove
 (`!l1 l2. SCRATCH_ETA4(APPEND l1 l2) =
           APPEND (SCRATCH_ETA4 l1) (SCRATCH_ETA4 l2)`,
  REWRITE_TAC[SCRATCH_ETA4; NIBBLES_APPEND; FILTER_APPEND; MAP_APPEND]);;

let LENGTH_SCRATCH_ETA4 = prove
 (`!l. LENGTH(SCRATCH_ETA4 l) = LENGTH(FILTER (\x:byte. val x < 9) (NIBBLES l))`,
  REWRITE_TAC[SCRATCH_ETA4; LENGTH_MAP]);;

let LENGTH_SCRATCH_ETA4_BOUND = prove
 (`!l. LENGTH(SCRATCH_ETA4 l) <= 2 * LENGTH l`,
  GEN_TAC THEN REWRITE_TAC[LENGTH_SCRATCH_ETA4] THEN
  TRANS_TAC LE_TRANS `LENGTH(NIBBLES l)` THEN
  REWRITE_TAC[LENGTH_FILTER; LENGTH_NIBBLES]);;

let REJ_SAMPLE_ETA4 = define
 `REJ_SAMPLE_ETA4 l =
    MAP (\x:byte. iword(&4 - &(val x)):int32)
        (FILTER (\x:byte. val x < 9) (NIBBLES l))`;;

let REJ_SAMPLE_ETA4_EMPTY = prove
 (`REJ_SAMPLE_ETA4 [] = []`,
  REWRITE_TAC[REJ_SAMPLE_ETA4; NIBBLES; FILTER; MAP]);;

let REJ_SAMPLE_ETA4_APPEND = prove
 (`!l1 l2. REJ_SAMPLE_ETA4(APPEND l1 l2) =
           APPEND (REJ_SAMPLE_ETA4 l1) (REJ_SAMPLE_ETA4 l2)`,
  REWRITE_TAC[REJ_SAMPLE_ETA4; NIBBLES_APPEND; FILTER_APPEND; MAP_APPEND]);;

let LENGTH_REJ_SAMPLE_ETA4 = prove
 (`!l. LENGTH(REJ_SAMPLE_ETA4 l) = LENGTH(SCRATCH_ETA4 l)`,
  REWRITE_TAC[REJ_SAMPLE_ETA4; SCRATCH_ETA4; LENGTH_MAP]);;
