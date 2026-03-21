(* Load proof up to back-edge subgoal *)
g `!res buf buflen table (inbytes:byte list) pc stackpointer.
        8 <= val buflen /\
        8 divides val buflen /\
        val buflen = LENGTH inbytes /\
        ALL (nonoverlapping (word_sub stackpointer (word 576),576))
            [(word pc,LENGTH mldsa_rej_uniform_eta4_mc);
             (buf,val buflen); (table,4096); (res,1024)] /\
        ALL (nonoverlapping (res,1024))
            [(word pc,LENGTH mldsa_rej_uniform_eta4_mc);
             (word_sub stackpointer (word 576),576)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) mldsa_rej_uniform_eta4_mc /\
                  read PC s = word pc /\
                  read SP s = stackpointer /\
                  C_ARGUMENTS [res;buf;buflen;table] s /\
                  read(memory :> bytes(table,4096)) s =
                  num_of_wordlist mldsa_rej_uniform_eta_table /\
                  read(memory :> bytes(buf,val buflen)) s =
                  num_of_wordlist inbytes)
             (\s. read PC s = word(pc + 340) /\
                  let outlist = SUB_LIST(0,256) (REJ_SAMPLE_ETA4 inbytes) in
                  let outlen = LENGTH outlist in
                  C_RETURN s = word outlen /\
                  read(memory :> bytes(res,4 * outlen)) s =
                  num_of_wordlist outlist)
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [SP] ,,
              MAYCHANGE [memory :> bytes(res,1024);
                         memory :> bytes(word_sub stackpointer (word 576),576)])`;;

e(REWRITE_TAC[LENGTH_MLDSA_REJ_UNIFORM_ETA4_MC; NONOVERLAPPING_CLAUSES;
              ALL; C_ARGUMENTS; C_RETURN] THEN
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `scratch:int64 = word_sub stackpointer (word 576)` THEN
  SUBGOAL_THEN
   `?i. val(buflen:int64) < 8 * (i + 1) \/
        256 <= LENGTH(SCRATCH_ETA4(SUB_LIST(0,8 * i) inbytes))`
  MP_TAC THENL
   [EXISTS_TAC `val(buflen:int64)` THEN ARITH_TAC;
    GEN_REWRITE_TAC LAND_CONV [num_WOP]] THEN
  DISCH_THEN(X_CHOOSE_THEN `N:num` (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  REWRITE_TAC[DE_MORGAN_THM; NOT_LE] THEN STRIP_TAC THEN
  MATCH_MP_TAC(MESON[]
   `!P'. (ensures arm P' Q R ==> ensures arm P Q R) /\ ensures arm P' Q R
        ==> ensures arm P Q R`) THEN
  EXISTS_TAC
   `\s. aligned_bytes_loaded s (word pc) mldsa_rej_uniform_eta4_mc /\
        read PC s = word (pc + 256) /\
        read SP s = (scratch:int64) /\
        read (memory :> bytes ((table:int64),4096)) s =
        num_of_wordlist mldsa_rej_uniform_eta_table /\
        read (memory :> bytes ((buf:int64),LENGTH(inbytes:byte list))) s =
        num_of_wordlist inbytes /\
        read Q7 s = word 20769504351625144638033088116686852 /\
        let outlist = SCRATCH_ETA4 (SUB_LIST (0,8 * N) inbytes) in
        let outlen = LENGTH outlist in
        read X0 s = (res:int64) /\
        read X3 s = (table:int64) /\
        read X4 s = word 256 /\
        read X8 s = (scratch:int64) /\
        read X9 s = word outlen /\
        read (memory :> bytes (scratch,2 * outlen)) s =
        num_of_wordlist outlist` THEN
  CONJ_TAC THENL
   [DISCH_TAC THEN
    REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
    ENSURES_WHILE_UP_TAC `N:num` `pc + 108` `pc + 248`
     `\i s.
        aligned_bytes_loaded s (word pc) mldsa_rej_uniform_eta4_mc /\
        read (memory :> bytes (table,4096)) s =
        num_of_wordlist mldsa_rej_uniform_eta_table /\
        read (memory :> bytes (buf,LENGTH inbytes)) s =
        num_of_wordlist inbytes /\
        read Q30 s = word 46731384791156575435574448262545417 /\
        read Q31 s = word 664619068533544770747334646890102785 /\
        read Q7 s = word 20769504351625144638033088116686852 /\
        let outlist = SCRATCH_ETA4 (SUB_LIST(0,8 * i) inbytes) in
        let outlen = LENGTH outlist in
        read X0 s = res /\
        read X1 s = word_add buf (word(8 * i)) /\
        read X2 s = word_sub buflen (word(8 * i)) /\
        read X3 s = table /\
        read X4 s = word 256 /\
        read X7 s = word_add scratch (word(2 * outlen)) /\
        read X8 s = scratch /\
        read X9 s = word outlen /\
        read SP s = scratch /\
        read (memory :> bytes (scratch,2 * outlen)) s =
        num_of_wordlist outlist` THEN
    REPEAT CONJ_TAC THENL
     [(* ~(N=0) *)
      DISCH_THEN SUBST_ALL_TAC THEN
      FIRST_X_ASSUM(MP_TAC o check (is_disj o concl)) THEN
      REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES; SUB_LIST_CLAUSES;
                   SCRATCH_ETA4_EMPTY; LENGTH;
                   ARITH_RULE `~(256 <= 0)`] THEN
      ASM_ARITH_TAC;

      (* Preamble *)
      FIRST_X_ASSUM(MP_TAC o SPEC `0`) THEN
      ASM_REWRITE_TAC[ADD_CLAUSES; MULT_CLAUSES] THEN STRIP_TAC THEN
      GHOST_INTRO_TAC `q31_init:int128` `read Q31` THEN
      ENSURES_INIT_TAC "s0" THEN
      ARM_STEPS_TAC MLDSA_REJ_UNIFORM_ETA4_EXEC (1--76) THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
      CONJ_TAC THENL [CONV_TAC WORD_BLAST; ALL_TAC] THEN
      REWRITE_TAC[MULT_CLAUSES; SUB_LIST_CLAUSES; SCRATCH_ETA4_EMPTY] THEN
      CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REWRITE_TAC[LENGTH] THEN
      REWRITE_TAC[MULT_CLAUSES; WORD_ADD_0; WORD_SUB_0] THEN
      REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_TRIVIAL; num_of_wordlist];

      (* Body - CHEAT for now *)
      CHEAT_TAC;

      (* Back-edge - leave open *)
      ALL_TAC;

      (* Exit - leave open *)
      ALL_TAC];

    (* Second half - leave open *)
    ALL_TAC]);;
