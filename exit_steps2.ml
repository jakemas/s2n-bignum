(* Exit proof: inv(N) at pc+248 -> P' at pc+256 *)
(* Two cases: *)
(*   - Not enough bytes: CMP X2,#8; B.HS not taken -> fall through (2 steps) *)
(*   - Enough bytes but outlen>=256: CMP X2,#8; B.HS taken -> pc+108; *)
(*     CMP X9,X4; B.HS taken -> pc+256 (4 steps) *)
e(CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  SUBGOAL_THEN `8 * N <= val(buflen:int64)` ASSUME_TAC THENL
   [ASM_CASES_TAC `N = 0` THEN ASM_REWRITE_TAC[MULT_CLAUSES; LE_0] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `N - 1`) THEN
    ASM_REWRITE_TAC[ARITH_RULE `n - 1 < n <=> ~(n = 0)`] THEN
    ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `val(word(8 * N):int64) = 8 * N` ASSUME_TAC THENL
   [REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN MATCH_MP_TAC MOD_LT THEN
    MP_TAC(ISPEC `buflen:int64` VAL_BOUND_64) THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  VAL_INT64_TAC
   `LENGTH (SCRATCH_ETA4 (SUB_LIST (0,8 * N) (inbytes:byte list)))` THEN
  ASM_CASES_TAC `val(buflen:int64) < 8 * (N + 1)` THENL
   [(* Case 1: not enough bytes remaining *)
    SUBGOAL_THEN
     `~(8 <= val(word_sub (buflen:int64) (word(8 * N))))`
    ASSUME_TAC THENL
     [ASM_REWRITE_TAC[VAL_WORD_SUB_CASES; NOT_LE] THEN
      COND_CASES_TAC THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    ENSURES_INIT_TAC "s0" THEN
    ARM_STEPS_TAC MLDSA_REJ_UNIFORM_ETA4_EXEC (1--2) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[];
    (* Case 2: enough bytes but outlen >= 256 *)
    SUBGOAL_THEN
     `8 <= val(word_sub (buflen:int64) (word(8 * N)))`
    ASSUME_TAC THENL
     [ASM_REWRITE_TAC[VAL_WORD_SUB_CASES] THEN
      COND_CASES_TAC THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o check (is_disj o concl)) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    ENSURES_INIT_TAC "s0" THEN
    ARM_STEPS_TAC MLDSA_REJ_UNIFORM_ETA4_EXEC (1--2) THEN
    ARM_STEPS_TAC MLDSA_REJ_UNIFORM_ETA4_EXEC (3--4) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[]]);;
