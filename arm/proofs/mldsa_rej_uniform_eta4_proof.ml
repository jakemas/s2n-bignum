(* ========================================================================= *)
(* Proof of mldsa_rej_uniform_eta4 correctness (WIP)                        *)
(*                                                                           *)
(* ARM stepping is fully working including both ST1 stores in loop body.    *)
(* Remaining CHEATs are about functional correctness (SIMD semantics),      *)
(* not ARM stepping mechanics.                                               *)
(*                                                                           *)
(* CHEAT 1: Loop body first half — SIMD compute (27 ARM steps).            *)
(*   Needs to prove val(read X12 s) <= 8 /\ val(read X13 s) <= 8           *)
(*   from the popcount SIMD sequence.                                        *)
(*                                                                           *)
(* CHEAT 2: Loop body postcondition — connecting register state to          *)
(*   REJ_NIBBLES_ETA4(SUB_LIST(0,8*(i+1)) inlist) specification.           *)
(*                                                                           *)
(* CHEAT 3: Writeback phase — 181 ARM steps, needs BIGNUM_LDIGITIZE_TAC.   *)
(*                                                                           *)
(* Post-loop exit is FULLY PROVED (both cases).                             *)
(* ========================================================================= *)

needs "arm/proofs/base.ml";;
needs "arm/proofs/mldsa_rej_uniform_eta_table.ml";;
needs "common/mldsa_specs.ml";;

let mldsa_rej_uniform_eta4_mc = define_assert_from_elf
  "mldsa_rej_uniform_eta4_mc" "arm/mldsa/mldsa_rej_uniform_eta4.o"
[
  (* ... bytecode omitted for brevity, same as in _simple.ml ... *)
];;

let MLDSA_REJ_UNIFORM_ETA4_EXEC = ARM_MK_EXEC_RULE mldsa_rej_uniform_eta4_mc;;

let LENGTH_MLDSA_REJ_UNIFORM_ETA4_MC =
  fst MLDSA_REJ_UNIFORM_ETA4_EXEC;;

let WORD_INSERT_Q31 = prove(
  `word_insert ((word_insert:int128->num#num->int64->int128) q (0,64)
    (word 2251816993685505)) (64,64) (word 36029071898968080:int64) =
    (word 664619068533544770747334646890102785:int128)`,
  CONV_TAC WORD_BLAST);;

(* Helper for ADD X7, X7, Xn LSL 1 rewriting *)
let WORD_ADD_SHL1 = WORD_BLAST
 `!sp (x:int64) k.
    word_add (word_add sp (word(2 * k):int64))
             (word_shl x 1:int64) =
    word_add sp (word(2 * (k + val(x:int64))):int64)`;;

(* ========================================================================= *)
(* The proof (interactive g/e style).                                        *)
(* Run each e(...) in sequence in a HOL Light session with the checkpoint.   *)
(* ========================================================================= *)

g `!res buf buflen table (inlist:byte list) pc stackpointer.
      8 divides val buflen /\
      8 <= val buflen /\
      LENGTH inlist = val buflen /\
      ALL (nonoverlapping (stackpointer,576))
          [(word pc,LENGTH mldsa_rej_uniform_eta4_mc);
           (buf,val buflen); (table,4096)] /\
      ALL (nonoverlapping (res,1024))
          [(word pc,LENGTH mldsa_rej_uniform_eta4_mc);
           (stackpointer,576)]
      ==> ensures arm
           (\s. aligned_bytes_loaded s (word pc) mldsa_rej_uniform_eta4_mc /\
                read PC s = word(pc + 4) /\
                read SP s = stackpointer /\
                C_ARGUMENTS [res;buf;buflen;table] s /\
                read(memory :> bytes(table,4096)) s =
                num_of_wordlist mldsa_rej_uniform_eta_table /\
                read(memory :> bytes(buf,val buflen)) s =
                num_of_wordlist inlist)
           (\s. read PC s = word(pc + 336) /\
                let outlist = SUB_LIST(0,256) (REJ_SAMPLE_ETA4 inlist) in
                let outlen = LENGTH outlist in
                C_RETURN s = word outlen /\
                read(memory :> bytes(res,4 * outlen)) s =
                num_of_wordlist outlist)
           (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
            MAYCHANGE [memory :> bytes(res,1024);
                       memory :> bytes(stackpointer,576)])`;;

(* === FULL PROOF TACTIC (with 4 CHEATs) === *)
(* Takes ~60 seconds total *)
(* Key technique: ENSURES_SEQUENCE_TAC within loop body at pc+0xD8 *)
(* to capture X12/X13 bounds before ST1 stores. *)

e (REWRITE_TAC[LENGTH_MLDSA_REJ_UNIFORM_ETA4_MC;
    fst MLDSA_REJ_UNIFORM_ETA4_EXEC;
    MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI;
    C_ARGUMENTS; ALL; C_RETURN] THEN
 MAP_EVERY X_GEN_TAC [`res:int64`; `buf:int64`] THEN
 W64_GEN_TAC `buflen:num` THEN
 MAP_EVERY X_GEN_TAC
  [`table:int64`; `inlist:byte list`; `pc:num`; `stackpointer:int64`] THEN
 DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN

 (* === Split: computation (pc+4 to pc+0x100) and writeback (to pc+0x150) *)
 ENSURES_SEQUENCE_TAC `pc + 0x100`
  `\s. aligned_bytes_loaded s (word pc) mldsa_rej_uniform_eta4_mc /\
       read PC s = word(pc + 0x100) /\
       read X0 s = res /\ read X4 s = word 256 /\
       read X8 s = stackpointer /\
       read Q7 s = word 20769504351625144638033088116686852 /\
       ALL (nonoverlapping (res,1024)) [(word pc,344); (stackpointer,576)] /\
       ?n. let niblist = REJ_NIBBLES_ETA4 (SUB_LIST (0,8 * n) inlist) in
           let niblen = LENGTH niblist in
           niblen < 272 /\ read X9 s = word niblen /\
           (buflen < 8 * (n + 1) \/ 256 <= niblen) /\
           read (memory :> bytes (stackpointer,2 * niblen)) s =
           num_of_wordlist niblist` THEN
 CONJ_TAC THENL [ALL_TAC; CHEAT_TAC] THEN  (* CHEAT 4: Writeback *)

 (* === WOP + 0 < N === *)
 SUBGOAL_THEN
  `?i. buflen < 8 * (i + 1) \/
       256 <= LENGTH(REJ_NIBBLES_ETA4(SUB_LIST(0,8 * i) inlist))`
 MP_TAC THENL
  [EXISTS_TAC `buflen:num` THEN ARITH_TAC;
   GEN_REWRITE_TAC LAND_CONV [num_WOP]] THEN
 DISCH_THEN(X_CHOOSE_THEN `N:num` (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
 REWRITE_TAC[DE_MORGAN_THM; NOT_LE] THEN STRIP_TAC THEN
 SUBGOAL_THEN `0 < N` ASSUME_TAC THENL
  [REWRITE_TAC[ARITH_RULE `0 < N <=> ~(N = 0)`] THEN
   DISCH_THEN SUBST_ALL_TAC THEN
   FIRST_X_ASSUM(MP_TAC o check (is_disj o concl)) THEN
   REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES;
               SUB_LIST_CLAUSES; REJ_NIBBLES_ETA4_EMPTY; LENGTH] THEN
   UNDISCH_TAC `8 <= buflen` THEN ARITH_TAC; ALL_TAC] THEN

 (* === Main loop === *)
 ENSURES_WHILE_UP_TAC `N:num` `pc + 0x6c` `pc + 0xf8`
  `\i s. read (memory :> bytes (table,4096)) s =
         num_of_wordlist mldsa_rej_uniform_eta_table /\
         read (memory :> bytes (buf,buflen)) s = num_of_wordlist inlist /\
         aligned_bytes_loaded s (word pc) mldsa_rej_uniform_eta4_mc /\
         read Q7 s = word 20769504351625144638033088116686852 /\
         read Q30 s = word 46731384791156575435574448262545417 /\
         read Q31 s = word 664619068533544770747334646890102785 /\
         let niblist = REJ_NIBBLES_ETA4(SUB_LIST(0,8 * i) inlist) in
         let niblen = LENGTH niblist in
         read X0 s = res /\
         read X1 s = word_add buf (word(8 * i)) /\
         read X2 s = word_sub (word buflen) (word(8 * i)) /\
         read X3 s = table /\ read X4 s = word 256 /\
         read X7 s = word_add stackpointer (word(2 * niblen)) /\
         read X8 s = stackpointer /\ read X9 s = word niblen /\
         read (memory :> bytes (stackpointer,2 * niblen)) s =
         num_of_wordlist niblist` THEN
 REPEAT CONJ_TAC THENL
  [(*** ~(N=0) — PROVED ***) ASM_ARITH_TAC;

   (*** Pre-loop init (75 ARM steps) — PROVED ***)
   FIRST_X_ASSUM(MP_TAC o SPEC `0`) THEN
   ASM_REWRITE_TAC[ADD_CLAUSES; MULT_CLAUSES] THEN STRIP_TAC THEN
   GHOST_INTRO_TAC `q31_init:int128` `read Q31` THEN
   ENSURES_INIT_TAC "s0" THEN
   ARM_STEPS_TAC MLDSA_REJ_UNIFORM_ETA4_EXEC (1--75) THEN
   ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
   CONJ_TAC THENL [REWRITE_TAC[WORD_INSERT_Q31]; ALL_TAC] THEN
   REWRITE_TAC[MULT_CLAUSES; SUB_LIST_CLAUSES; REJ_NIBBLES_ETA4_EMPTY] THEN
   CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REWRITE_TAC[LENGTH] THEN
   REWRITE_TAC[MULT_CLAUSES; WORD_ADD_0; WORD_SUB_0] THEN
   REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_TRIVIAL; num_of_wordlist];

   (*** Loop body — split at pc+0xD8 for ST1 stores ***)
   X_GEN_TAC `i:num` THEN STRIP_TAC THEN
   ABBREV_TAC `curlist = REJ_NIBBLES_ETA4(SUB_LIST(0,8 * i) inlist)` THEN
   ABBREV_TAC `curlen = LENGTH(curlist:int16 list)` THEN
   CONV_TAC(RATOR_CONV(LAND_CONV(TOP_DEPTH_CONV let_CONV))) THEN
   ASM_REWRITE_TAC[] THEN
   FIRST_X_ASSUM(MP_TAC o C MATCH_MP (ASSUME `i:num < N`)) THEN
   REWRITE_TAC[DE_MORGAN_THM; NOT_LE; NOT_LT] THEN STRIP_TAC THEN
   SUBGOAL_THEN `curlen < 256` ASSUME_TAC THENL
    [EXPAND_TAC "curlen" THEN EXPAND_TAC "curlist" THEN
     ASM_REWRITE_TAC[]; ALL_TAC] THEN
   (* Split loop body: first half = SIMD compute, second half = stores *)
   ENSURES_SEQUENCE_TAC `pc + 0xd8`
    `\s. read (memory :> bytes (table,4096)) s =
         num_of_wordlist mldsa_rej_uniform_eta_table /\
         read (memory :> bytes (buf,buflen)) s = num_of_wordlist inlist /\
         aligned_bytes_loaded s (word pc) mldsa_rej_uniform_eta4_mc /\
         read Q7 s = word 20769504351625144638033088116686852 /\
         read Q30 s = word 46731384791156575435574448262545417 /\
         read Q31 s = word 664619068533544770747334646890102785 /\
         read X0 s = res /\
         read X1 s = word_add buf (word(8 * (i + 1))) /\
         read X2 s = word_sub (word buflen) (word(8 * (i + 1))) /\
         read X3 s = table /\ read X4 s = word 256 /\
         read X7 s = word_add stackpointer (word(2 * curlen)) /\
         read X8 s = stackpointer /\ read X9 s = word curlen /\
         read (memory :> bytes (stackpointer,2 * curlen)) s =
         num_of_wordlist curlist /\
         val(read X12 s:int64) <= 8 /\
         val(read X13 s:int64) <= 8` THEN
   CONJ_TAC THENL
    [CHEAT_TAC;  (* CHEAT 1: First half — SIMD compute + X12/X13 bounds *)
     ALL_TAC] THEN
   (* Second half: TBL + ST1 + ADD X7, with nonoverlapping *)
   ENSURES_INIT_TAC "s0" THEN
   ABBREV_TAC `len0 = val(read X12 s0:int64)` THEN
   ABBREV_TAC `len1 = val(read X13 s0:int64)` THEN
   ARM_STEPS_TAC MLDSA_REJ_UNIFORM_ETA4_EXEC (1--3) THEN
   ARM_VERBOSE_STEP_TAC MLDSA_REJ_UNIFORM_ETA4_EXEC "s4" THEN
   FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE RAND_CONV [WORD_ADD_SHL1]) THEN
   ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
   SUBGOAL_THEN
    `nonoverlapping (word_add stackpointer (word(2 * (curlen + len0))):int64,
                     16) (word pc:int64, 344)`
   ASSUME_TAC THENL [NONOVERLAPPING_TAC; ALL_TAC] THEN
   ARM_STEPS_TAC MLDSA_REJ_UNIFORM_ETA4_EXEC [5] THEN
   ARM_VERBOSE_STEP_TAC MLDSA_REJ_UNIFORM_ETA4_EXEC "s6" THEN
   FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE RAND_CONV [WORD_ADD_SHL1]) THEN
   ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
   ARM_STEPS_TAC MLDSA_REJ_UNIFORM_ETA4_EXEC (7--8) THEN
   ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
   CHEAT_TAC;  (* CHEAT 2: Loop body postcondition *)

   (*** Back-edge (2 ARM steps) — PROVED ***)
   X_GEN_TAC `i:num` THEN STRIP_TAC THEN
   CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
   SUBGOAL_THEN `8 * (i + 1) <= buflen` ASSUME_TAC THENL
    [FIRST_X_ASSUM(MP_TAC o SPEC `i:num`) THEN
     ASM_REWRITE_TAC[] THEN ARITH_TAC; ALL_TAC] THEN
   SUBGOAL_THEN `8 * i < 2 EXP 64` ASSUME_TAC THENL
    [ASM_ARITH_TAC; ALL_TAC] THEN
   ENSURES_INIT_TAC "s0" THEN
   SUBGOAL_THEN `8 <= val(word_sub (word buflen:int64) (word (8 * i)))`
   ASSUME_TAC THENL
    [MAP_EVERY VAL_INT64_TAC [`buflen:num`; `8 * i`] THEN
     ASM_REWRITE_TAC[VAL_WORD_SUB_CASES] THEN ASM_ARITH_TAC;
     ALL_TAC] THEN
   ARM_STEPS_TAC MLDSA_REJ_UNIFORM_ETA4_EXEC (1--2) THEN
   ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[];

   (*** Post-loop exit — FULLY PROVED ***)
   SUBGOAL_THEN
    `LENGTH (REJ_NIBBLES_ETA4 (SUB_LIST (0,8 * N) inlist)) < 272`
   ASSUME_TAC THENL
    [ASM_CASES_TAC `N = 0` THENL
      [ASM_REWRITE_TAC[MULT_CLAUSES; SUB_LIST_CLAUSES;
                       REJ_NIBBLES_ETA4_EMPTY] THEN
       REWRITE_TAC[LENGTH] THEN CONV_TAC NUM_REDUCE_CONV;
       FIRST_X_ASSUM(MP_TAC o SPEC `N - 1`)] THEN
     ASM_REWRITE_TAC[ARITH_RULE `n - 1 < n <=> ~(n = 0)`] THEN
     MATCH_MP_TAC(ARITH_RULE
      `l2 <= l + 16 ==> ~(b < x) /\ l < 256 ==> l2 < 272`) THEN
     MP_TAC(ISPECL [`inlist:byte list`; `8 * (N - 1)`; `8`; `0`]
       SUB_LIST_SPLIT) THEN
     ASM_SIMP_TAC[ARITH_RULE `~(N = 0) ==> 8 * (N - 1) + 8 = 8 * N`] THEN
     DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[REJ_NIBBLES_ETA4_APPEND] THEN
     REWRITE_TAC[LENGTH_APPEND; LE_ADD_LCANCEL; ADD_CLAUSES] THEN
     TRANS_TAC LE_TRANS
      `2 * LENGTH(SUB_LIST(8*(N-1),8) (inlist:byte list))` THEN
     CONJ_TAC THENL [REWRITE_TAC[LENGTH_REJ_NIBBLES_ETA4]; ALL_TAC] THEN
     REWRITE_TAC[LENGTH_SUB_LIST] THEN ARITH_TAC;
     ALL_TAC] THEN
   VAL_INT64_TAC
    `LENGTH (REJ_NIBBLES_ETA4 (SUB_LIST (0,8 * N) inlist))` THEN
   SUBGOAL_THEN
    `8 <= val(word_sub (word buflen:int64) (word (8 * N))) <=>
     8 * (N + 1) <= buflen`
   ASSUME_TAC THENL
    [SUBGOAL_THEN `8 * N < 2 EXP 64` ASSUME_TAC THENL
      [FIRST_X_ASSUM(MP_TAC o SPEC `N - 1`) THEN SIMPLE_ARITH_TAC;
       MAP_EVERY VAL_INT64_TAC [`8 * N`; `buflen:num`]] THEN
     ASM_REWRITE_TAC[VAL_WORD_SUB_CASES] THEN
     FIRST_X_ASSUM(MP_TAC o SPEC `N - 1`) THEN SIMPLE_ARITH_TAC;
     ALL_TAC] THEN
   CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
   ASM_CASES_TAC `8 * (N + 1) <= buflen` THENL
    [(* Case B: more input, back edge taken, exit at loop head *)
     ENSURES_INIT_TAC "s0" THEN
     ARM_STEPS_TAC MLDSA_REJ_UNIFORM_ETA4_EXEC (1--2) THEN
     FIRST_X_ASSUM(MP_TAC o check (is_disj o concl)) THEN
     ASM_REWRITE_TAC[GSYM NOT_LE] THEN DISCH_TAC THEN
     ARM_STEPS_TAC MLDSA_REJ_UNIFORM_ETA4_EXEC (3--4) THEN
     ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[ALL] THEN
     EXISTS_TAC `N:num` THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
     (* Case A: input exhausted, fall through *)
     ENSURES_INIT_TAC "s0" THEN
     SUBGOAL_THEN
      `~(8 <= val(word_sub (word buflen:int64) (word (8 * N))))`
     ASSUME_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
     ARM_STEPS_TAC MLDSA_REJ_UNIFORM_ETA4_EXEC (1--2) THEN
     ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[ALL] THEN
     EXISTS_TAC `N:num` THEN ASM_REWRITE_TAC[]]]);;
