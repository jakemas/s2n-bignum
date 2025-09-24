(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* ML-DSA Forward number theoretic transform.                                *)
(* ========================================================================= *)

needs "x86/proofs/base.ml";;
needs "common/mlkem_mldsa.ml";;

(*** print_literal_from_elf "x86/mldsa/mldsa_ntt.o";; ***)

let mldsa_ntt_mc = define_assert_from_elf "mldsa_ntt_mc" "x86/mldsa/mldsa_ntt.o"


let mldsa_ntt_tmc = define_trimmed "mldsa_ntt_tmc" mldsa_ntt_mc;;
let MLDSA_NTT_TMC_EXEC = X86_MK_CORE_EXEC_RULE mldsa_ntt_tmc;;

(*** getting PC length/size:
let len_thm = REWRITE_CONV[mldsa_ntt_tmc] `LENGTH mldsa_ntt_tmc` in
let len_computed = LENGTH_CONV (rhs (concl len_thm)) in
let final_value = rhs (concl len_computed) in
dest_small_numeral final_value;;

val it : int = 12401
pc + 0x3070 ***)

(* ------------------------------------------------------------------------- *)
(* Data tables that are assumed in the precondition.                         *)
(* ------------------------------------------------------------------------- *)

let mldsa_zetas_optimized_twiddles = define
 `mldsa_zetas_optimized_twiddles:int list =
   [-- &3975713; &25847; -- &2608894; -- &518909; &237124; -- &777960; -- &876248; &466468; &1826347;
    &1826347; &1826347; &1826347; &2353451; &2353451; &2353451; &2353451; -- &359251;
    -- &359251; -- &359251; -- &359251; -- &2091905; -- &2091905; -- &2091905; -- &2091905; &3119733;
    &3119733; &3119733; &3119733; -- &2884855; -- &2884855; -- &2884855; -- &2884855; &3111497;
    &3111497; &3111497; &3111497; &2680103; &2680103; &2680103; &2680103; &2725464;
    &2725464; &1024112; &1024112; -- &1079900; -- &1079900; &3585928; &3585928; -- &549488;
    -- &549488; -- &1119584; -- &1119584; &2619752; &2619752; -- &2108549; -- &2108549; -- &2118186;
    -- &2118186; -- &3859737; -- &3859737; -- &1399561; -- &1399561; -- &3277672; -- &3277672; &1757237;
    &1757237; -- &19422; -- &19422; &4010497; &4010497; &280005; &280005; &2706023;
    &95776; &3077325; &3530437; -- &1661693; -- &3592148; -- &2537516; &3915439; -- &3861115;
    -- &3043716; &3574422; -- &2867647; &3539968; -- &300467; &2348700; -- &539299; -- &1699267;
    -- &1643818; &3505694; -- &3821735; &3507263; -- &2140649; -- &1600420; &3699596; &811944;
    &531354; &954230; &3881043; &3900724; -- &2556880; &2071892; -- &2797779; -- &3930395;
    -- &3677745; -- &1452451; &2176455; -- &1257611; -- &4083598; -- &3190144; -- &3632928; &3412210;
    &2147896; -- &2967645; -- &411027; -- &671102; -- &22981; -- &381987; &1852771; -- &3343383;
    &508951; &44288; &904516; -- &3724342; &1653064; &2389356; &759969; &189548;
    &3159746; -- &2409325; &1315589; &1285669; -- &812732; -- &3019102; -- &3628969; -- &1528703;
    -- &3041255; &3475950; -- &1585221; &1939314; -- &1000202; -- &3157330; &126922; -- &983419;
    &2715295; -- &3693493; -- &2477047; -- &1228525; -- &1308169; &1349076; -- &1430430; &264944;
    &3097992; -- &1100098; &3958618; -- &8578; -- &3249728; -- &210977; -- &1316856; -- &3553272;
    -- &1851402; -- &177440; &1341330; -- &1584928; -- &1439742; -- &3881060; &3839961; &2091667;
    -- &3342478; &266997; -- &3520352; &900702; &495491; -- &655327; -- &3556995; &342297;
    &3437287; &2842341; &4055324; -- &3767016; -- &2994039; -- &1333058; -- &451100; -- &1279661;
    &1500165; -- &542412; -- &2584293; -- &2013608; &1957272; -- &3183426; &810149; -- &3038916;
    &2213111; -- &426683; -- &1667432; -- &2939036; &183443; -- &554416; &3937738; &3407706;
    &2244091; &2434439; -- &3759364; &1859098; -- &1613174; -- &3122442; -- &525098; &286988;
    -- &3342277; &2691481; &1247620; &1250494; &1869119; &1237275; &1312455; &1917081;
    &777191; -- &2831860; -- &3724270; &2432395; &3369112; &162844; &1652634; &3523897;
    -- &975884; &1723600; -- &1104333; -- &2235985; -- &976891; &3919660; &1400424; &2316500;
    -- &2446433; -- &1235728; -- &1197226; &909542; -- &43260; &2031748; -- &768622; -- &2437823;
    &1735879; -- &2590150; &2486353; &2635921; &1903435; -- &3318210; &3306115; -- &2546312;
    &2235880; -- &1671176; &594136; &2454455; &185531; &1616392; -- &3694233; &3866901;
    &1717735; -- &1803090; -- &260646; -- &420899; &1612842; -- &48306; -- &846154; &3817976;
    -- &3562462; &3513181; -- &3193378; &819034; -- &522500; &3207046; -- &3595838; &4108315;
    &203044; &1265009; &1595974; -- &3548272; -- &1050970; -- &1430225; -- &1962642; -- &1374803;
    &3406031; -- &1846953; -- &3776993; -- &164721; -- &1207385; &3014001; -- &1799107; &269760;
    &472078; &1910376; -- &3833893; -- &2286327; -- &3545687; -- &1362209; &1976782
   ]`;;

(* ------------------------------------------------------------------------- *)
(* Correctness proof.                                                        *)
(* ------------------------------------------------------------------------- *)

g(`!a zetas (zetas_list:int32 list) x pc.
      aligned 32 a /\
      aligned 32 zetas /\
      nonoverlapping (word pc,0x3070) (a, 1024) /\
      nonoverlapping (word pc,0x3070) (zetas, 1344) /\
      nonoverlapping (a, 1024) (zetas, 1344)
      ==> ensures x86
           (\s. bytes_loaded s (word pc) (BUTLAST mldsa_ntt_tmc) /\
                read RIP s = word pc /\
                C_ARGUMENTS [a; zetas] s /\
                wordlist_from_memory(zetas,296) s = zetas_list /\
                !i. i < 256
                    ==> read(memory :> bytes32(word_add a (word(4 * i)))) s =
                        x i)
           (\s. read RIP s = word(pc + 0x3070) /\
                (zetas_list = MAP iword mldsa_zetas_optimized_twiddles /\
                 (!i. i < 256 ==> abs(ival(x i)) <= &8380416)
                 ==> !i. i < 256
                         ==> let zi =
                        read(memory :> bytes32(word_add a (word(4 * i)))) s in
                        (ival zi == mldsa_forward_ntt (ival o x) i) (mod &8380417) /\
                        abs(ival zi) <= &6283008))
           (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
            MAYCHANGE [ZMM0; ZMM1; ZMM4; ZMM5; ZMM6; ZMM7; ZMM8; ZMM9; ZMM10; ZMM11; ZMM12; ZMM13; ZMM14; ZMM15] ,,
            MAYCHANGE [RAX] ,, MAYCHANGE SOME_FLAGS ,,
            MAYCHANGE [memory :> bytes(a,1024)])`);;

e(REWRITE_TAC[wordlist_from_memory]);;

   (* Step 1: First apply the working tactic *)
e(MAP_EVERY X_GEN_TAC
   [`a:int64`; `zetas:int64`; `zetas_list:int32 list`; `x:num->int32`; `pc:num`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              NONOVERLAPPING_CLAUSES; ALL] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC));;

(* now getting stuck on Stepping to state s4, first load of Zetas? *)

e(ASM_CASES_TAC
   `zetas_data:int32 list = MAP iword mldsa_zetas_optimized_twiddles` THEN
  ASM_REWRITE_TAC[CONJ_ASSOC] THEN REWRITE_TAC[GSYM CONJ_ASSOC] THENL
   [FIRST_X_ASSUM SUBST1_TAC;
    X86_QUICKSIM_TAC MLDSA_NTT_TMC_EXEC
     [`read RDI s = a`; `read RSI s = zetas`]
     (1--50)]);;

----- next atempt -----

g(`!a zetas (zetas_list:int32 list) x pc.
      aligned 32 a /\
      aligned 32 zetas /\
      nonoverlapping (word pc,0x3070) (a, 1024) /\
      nonoverlapping (word pc,0x3070) (zetas, 1344) /\
      nonoverlapping (a, 1024) (zetas, 1344)
      ==> ensures x86
           (\s. bytes_loaded s (word pc) (BUTLAST mldsa_ntt_tmc) /\
                read RIP s = word pc /\
                C_ARGUMENTS [a; zetas] s /\
                wordlist_from_memory(zetas,336) s = zetas_list /\
                !i. i < 256
                    ==> read(memory :> bytes32(word_add a (word(4 * i)))) s =
                        x i)
           (\s. read RIP s = word(pc + 0x3070) /\
                (zetas_list = MAP iword mldsa_zetas_optimized_twiddles /\
                 (!i. i < 256 ==> abs(ival(x i)) <= &8380416)
                 ==> !i. i < 256
                         ==> let zi =
                        read(memory :> bytes32(word_add a (word(4 * i)))) s in
                        (ival zi == mldsa_forward_ntt (ival o x) i) (mod &8380417) /\
                        abs(ival zi) <= &6283008))
           (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
            MAYCHANGE [ZMM0; ZMM1; ZMM4; ZMM5; ZMM6; ZMM7; ZMM8; ZMM9; ZMM10; ZMM11; ZMM12; ZMM13; ZMM14; ZMM15] ,,
            MAYCHANGE [RAX] ,, MAYCHANGE SOME_FLAGS ,,
            MAYCHANGE [memory :> bytes(a,1024)])`);;

(* Step 1: Setup - introduce variables and break down assumptions *)
e(MAP_EVERY X_GEN_TAC
   [`a:int64`; `zetas:int64`; `zetas_list:int32 list`; `x:num->int32`; `pc:num`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              NONOVERLAPPING_CLAUSES; ALL] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC));;

(* Step 2: Case splitting on zetas constraint (ML-KEM style) *)
e(ASM_CASES_TAC
   `zetas_list:int32 list = MAP iword mldsa_zetas_optimized_twiddles` THEN
  ASM_REWRITE_TAC[CONJ_ASSOC] THEN REWRITE_TAC[GSYM CONJ_ASSOC] THENL
   [FIRST_X_ASSUM SUBST1_TAC;
    ALL_TAC]);;

(* Step 3: Memory setup (similar to ML-KEM's approach) *)
e(CONV_TAC(ONCE_DEPTH_CONV let_CONV) THEN
  CONV_TAC(ONCE_DEPTH_CONV WORDLIST_FROM_MEMORY_CONV) THEN
  REWRITE_TAC[mldsa_zetas_optimized_twiddles] THEN
  REWRITE_TAC[MAP; CONS_11] THEN CONV_TAC(ONCE_DEPTH_CONV WORD_IWORD_CONV) THEN
  REWRITE_TAC[WORD_ADD_0] THEN ENSURES_INIT_TAC "s0");;

(* Step 4: simulate! *)
e(X86_STEPS_TAC MLDSA_NTT_TMC_EXEC (1-2337));;
e(ENSURES_FINAL_STATE_TAC);;
e(ASM_REWRITE_TAC[]);;

(* this fails at step 4*)
e(X86_QUICKSIM_TAC MLDSA_NTT_TMC_EXEC
   [`read RDI s0 = a`; `read RSI s0 = zetas`]
   (1--100));;

(* this works and simulates faster*)
e(MAP_EVERY (fun n ->
X86_STEPS_TAC MLDSA_NTT_TMC_EXEC [n] THEN
SIMD_SIMPLIFY_TAC[mldsa_montred])
        (1--2337));;


(* added to bignum.ml

let MEMORY_256_FROM_32_TAC =
  let a_tm = `a:int64` and n_tm = `n:num` and i64_ty = `:int64`
  and pat = `read (memory :> bytes256(word_add a (word n))) s0` in
  fun v n ->
    let pat' = subst[mk_var(v,i64_ty),a_tm] pat in
    let f i =
      let itm = mk_small_numeral(32*i) in
      READ_MEMORY_MERGE_CONV 7 (subst[itm,n_tm] pat') in
    MP_TAC(end_itlist CONJ (map f (0--(n-1))));;

*)

(* not sure where to go next *)

---- new version

g(`!a zetas (zetas_list:int32 list) x pc.
      aligned 32 a /\
      aligned 32 zetas /\
      nonoverlapping (word pc,0x3070) (a, 1024) /\
      nonoverlapping (word pc,0x3070) (zetas, 1344) /\
      nonoverlapping (a, 1024) (zetas, 1344)
      ==> ensures x86
           (\s. bytes_loaded s (word pc) (BUTLAST mldsa_ntt_tmc) /\
                read RIP s = word pc /\
                C_ARGUMENTS [a; zetas] s /\
                wordlist_from_memory(zetas,296) s = MAP (iword: int -> 32 word) mldsa_zetas_optimized_twiddles /\
                 (!i. i < 256 ==> abs(ival(x i)) <= &8380416) /\
                !i. i < 256
                    ==> read(memory :> bytes32(word_add a (word(4 * i)))) s =
                        x i)
           (\s. read RIP s = word(pc + 0x3070) /\
                (!i. i < 256
                         ==> let zi =
                        read(memory :> bytes32(word_add a (word(4 * i)))) s in
                        (ival zi == mldsa_forward_ntt (ival o x) i) (mod &8380417) /\
                        abs(ival zi) <= &6283008))
           (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
            MAYCHANGE [ZMM0; ZMM1; ZMM4; ZMM5; ZMM6; ZMM7; ZMM8; ZMM9; ZMM10; ZMM11; ZMM12; ZMM13; ZMM14; ZMM15] ,,
            MAYCHANGE [RAX] ,, MAYCHANGE SOME_FLAGS ,,
            MAYCHANGE [memory :> bytes(a,1024)])`);;

(* Step 1: Setup - introduce variables and break down assumptions *)
e(MAP_EVERY X_GEN_TAC
   [`a:int64`; `zetas:int64`; `zetas_list:int32 list`; `x:num->int32`; `pc:num`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              NONOVERLAPPING_CLAUSES; ALL] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC));;

(* Step 2: Memory setup (similar to ML-KEM's approach) *)
e(
  CONV_TAC(ONCE_DEPTH_CONV let_CONV) THEN
  CONV_TAC(ONCE_DEPTH_CONV WORDLIST_FROM_MEMORY_CONV) THEN
  REWRITE_TAC[MAP; CONS_11] THEN CONV_TAC(ONCE_DEPTH_CONV WORD_IWORD_CONV) THEN
  REWRITE_TAC[mldsa_zetas_optimized_twiddles] THEN
  CONV_TAC(RATOR_CONV(LAND_CONV(ONCE_DEPTH_CONV
   (EXPAND_CASES_CONV THENC ONCE_DEPTH_CONV NUM_MULT_CONV)))) THEN
  REWRITE_TAC[MAP; CONS_11] THEN CONV_TAC(ONCE_DEPTH_CONV WORD_IWORD_CONV)
);;

(* Step 3: Initialize state and restructure memory for vector loads *)
e(ENSURES_INIT_TAC "s0");;

(* Step 4: Restructure memory to match 256-bit loads *)
e(MP_TAC(end_itlist CONJ (map (fun n -> 
    READ_MEMORY_MERGE_CONV 3 (subst[mk_small_numeral(32*n),`n:num`] 
      `read (memory :> bytes256(word_add zetas (word n))) s0`)) (0--31))) THEN
  ASM_REWRITE_TAC[WORD_ADD_0] THEN 
  DISCARD_MATCHING_ASSUMPTIONS [`read (memory :> bytes32 a) s = x`] THEN 
  STRIP_TAC);;

(* Step 5: Execute assembly simulation *)
e(MAP_EVERY (fun n ->
X86_STEPS_TAC MLDSA_NTT_TMC_EXEC [n] THEN
SIMD_SIMPLIFY_TAC[mldsa_montred])
        (1--2337));;

(* Step 6: Complete the proof *)
e(ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[]);;
