(* ========================================================================= *)
(* Proof of mldsa_rej_uniform_eta4 correctness (WIP)                        *)
(*                                                                           *)
(* PROVED: Pre-loop init (75 ARM steps), back-edge (2 steps),               *)
(*   post-loop exit (2 steps), writeback X0 return value (245 ARM steps).   *)
(*                                                                           *)
(* Remaining CHEATs:                                                        *)
(*                                                                           *)
(* CHEAT 1: Loop body postcondition — connecting TBL shuffle + SIMD state   *)
(*   to REJ_NIBBLES_ETA4(SUB_LIST(0,8*(i+1)) inlist) specification.        *)
(*   Needs: LIST_EQ + EXPAND_CASES_CONV for TBL table correctness.         *)
(*                                                                           *)
(* CHEAT 2: Writeback memory content — connecting ARM SUB+SSHLL output     *)
(*   to num_of_wordlist(SUB_LIST(0,256)(REJ_SAMPLE_ETA4 inlist)).           *)
(*   Key lemmas proved: WORD_SX_SUB4_SMALL (BITBLAST_RULE),                *)
(*   SSHLL_LOWER/UPPER, SUB_LIST_MAP, ALL_REJ_NIBBLES_ETA4.               *)
(* ========================================================================= *)

needs "arm/proofs/base.ml";;
needs "arm/proofs/mldsa_rej_uniform_eta_table.ml";;

(**** print_literal_from_elf "arm/mldsa/mldsa_rej_uniform_eta4.o";;
 ****)

let mldsa_rej_uniform_eta4_mc = define_assert_from_elf
  "mldsa_rej_uniform_eta4_mc" "arm/mldsa/mldsa_rej_uniform_eta4.o"
(*** BYTECODE START ***)
[
  0xd10903ff;       (* arm_SUB SP SP (rvalue (word 576)) *)
  0xd2800027;       (* arm_MOV X7 (rvalue (word 1)) *)
  0xf2a00047;       (* arm_MOVK X7 (word 2) 16 *)
  0xf2c00087;       (* arm_MOVK X7 (word 4) 32 *)
  0xf2e00107;       (* arm_MOVK X7 (word 8) 48 *)
  0x4e081cff;       (* arm_INS_GEN Q31 X7 0 64 *)
  0xd2800207;       (* arm_MOV X7 (rvalue (word 16)) *)
  0xf2a00407;       (* arm_MOVK X7 (word 32) 16 *)
  0xf2c00807;       (* arm_MOVK X7 (word 64) 32 *)
  0xf2e01007;       (* arm_MOVK X7 (word 128) 48 *)
  0x4e181cff;       (* arm_INS_GEN Q31 X7 64 64 *)
  0x4f00853e;       (* arm_MOVI Q30 (word 2533313445691401) *)
  0x4f008487;       (* arm_MOVI Q7 (word 1125917086973956) *)
  0x910003e8;       (* arm_ADD X8 SP (rvalue (word 0)) *)
  0xaa0803e7;       (* arm_MOV X7 X8 *)
  0xd280000b;       (* arm_MOV X11 (rvalue (word 0)) *)
  0x6e301e10;       (* arm_EOR_VEC Q16 Q16 Q16 128 *)
  0x3c8404f0;       (* arm_STR Q16 X7 (Postimmediate_Offset (word 64)) *)
  0x3c9d00f0;       (* arm_STR Q16 X7 (Immediate_Offset (word 18446744073709551568)) *)
  0x3c9e00f0;       (* arm_STR Q16 X7 (Immediate_Offset (word 18446744073709551584)) *)
  0x3c9f00f0;       (* arm_STR Q16 X7 (Immediate_Offset (word 18446744073709551600)) *)
  0x9100816b;       (* arm_ADD X11 X11 (rvalue (word 32)) *)
  0xf104017f;       (* arm_CMP X11 (rvalue (word 256)) *)
  0x54ffff4b;       (* arm_BLT (word 2097128) *)
  0xaa0803e7;       (* arm_MOV X7 X8 *)
  0xd2800009;       (* arm_MOV X9 (rvalue (word 0)) *)
  0xd2802004;       (* arm_MOV X4 (rvalue (word 256)) *)
  0xeb04013f;       (* arm_CMP X9 X4 *)
  0x54000482;       (* arm_BCS (word 144) *)
  0xd1002042;       (* arm_SUB X2 X2 (rvalue (word 8)) *)
  0x0cdf7020;       (* arm_LDR D0 X1 (Postimmediate_Offset (word 8)) *)
  0x0f00e5fa;       (* arm_MOVI Q26 (word 1085102592571150095) *)
  0x0e3a1c1b;       (* arm_AND_VEC Q27 Q0 Q26 64 *)
  0x2f0c041c;       (* arm_USHR_VEC Q28 Q0 4 8 64 *)
  0x0e1c3b7a;       (* arm_ZIP1 Q26 Q27 Q28 8 64 *)
  0x0e1c7b7d;       (* arm_ZIP2 Q29 Q27 Q28 8 64 *)
  0x2f08a750;       (* arm_USHLL_VEC Q16 Q26 0 8 *)
  0x2f08a7b1;       (* arm_USHLL_VEC Q17 Q29 0 8 *)
  0x6e7037c4;       (* arm_CMHI_VEC Q4 Q30 Q16 16 128 *)
  0x6e7137c5;       (* arm_CMHI_VEC Q5 Q30 Q17 16 128 *)
  0x4e3f1c84;       (* arm_AND_VEC Q4 Q4 Q31 128 *)
  0x4e3f1ca5;       (* arm_AND_VEC Q5 Q5 Q31 128 *)
  0x6e703894;       (* arm_UADDLV Q20 Q4 8 16 *)
  0x6e7038b5;       (* arm_UADDLV Q21 Q5 8 16 *)
  0x1e26028c;       (* arm_FMOV_FtoI W12 Q20 0 32 *)
  0x1e2602ad;       (* arm_FMOV_FtoI W13 Q21 0 32 *)
  0x3cec7878;       (* arm_LDR Q24 X3 (Shiftreg_Offset X12 4) *)
  0x3ced7879;       (* arm_LDR Q25 X3 (Shiftreg_Offset X13 4) *)
  0x4e205884;       (* arm_CNT Q4 Q4 128 *)
  0x4e2058a5;       (* arm_CNT Q5 Q5 128 *)
  0x6e703894;       (* arm_UADDLV Q20 Q4 8 16 *)
  0x6e7038b5;       (* arm_UADDLV Q21 Q5 8 16 *)
  0x1e26028c;       (* arm_FMOV_FtoI W12 Q20 0 32 *)
  0x1e2602ad;       (* arm_FMOV_FtoI W13 Q21 0 32 *)
  0x4e180210;       (* arm_TBL Q16 [Q16] Q24 128 *)
  0x4e190231;       (* arm_TBL Q17 [Q17] Q25 128 *)
  0x4c0074f0;       (* arm_STR Q16 X7 No_Offset *)
  0x8b0c04e7;       (* arm_ADD X7 X7 (Shiftedreg X12 LSL 1) *)
  0x4c0074f1;       (* arm_STR Q17 X7 No_Offset *)
  0x8b0d04e7;       (* arm_ADD X7 X7 (Shiftedreg X13 LSL 1) *)
  0x8b0d018c;       (* arm_ADD X12 X12 X13 *)
  0x8b0c0129;       (* arm_ADD X9 X9 X12 *)
  0xf100205f;       (* arm_CMP X2 (rvalue (word 8)) *)
  0x54fffb82;       (* arm_BCS (word 2097008) *)
  0xeb04013f;       (* arm_CMP X9 X4 *)
  0x9a843129;       (* arm_CSEL X9 X9 X4 Condition_CC *)
  0xd280000b;       (* arm_MOV X11 (rvalue (word 0)) *)
  0xaa0803e7;       (* arm_MOV X7 X8 *)
  0x3cc204f0;       (* arm_LDR Q16 X7 (Postimmediate_Offset (word 32)) *)
  0x3cdf00f2;       (* arm_LDR Q18 X7 (Immediate_Offset (word 18446744073709551600)) *)
  0x6e7084f0;       (* arm_SUB_VEC Q16 Q7 Q16 16 128 *)
  0x6e7284f2;       (* arm_SUB_VEC Q18 Q7 Q18 16 128 *)
  0x4f10a611;       (* arm_SSHLL2_VEC Q17 Q16 0 16 *)
  0x0f10a610;       (* arm_SSHLL_VEC Q16 Q16 0 16 *)
  0x4f10a653;       (* arm_SSHLL2_VEC Q19 Q18 0 16 *)
  0x0f10a652;       (* arm_SSHLL_VEC Q18 Q18 0 16 *)
  0x3c840410;       (* arm_STR Q16 X0 (Postimmediate_Offset (word 64)) *)
  0x3c9d0011;       (* arm_STR Q17 X0 (Immediate_Offset (word 18446744073709551568)) *)
  0x3c9e0012;       (* arm_STR Q18 X0 (Immediate_Offset (word 18446744073709551584)) *)
  0x3c9f0013;       (* arm_STR Q19 X0 (Immediate_Offset (word 18446744073709551600)) *)
  0x9100416b;       (* arm_ADD X11 X11 (rvalue (word 16)) *)
  0xf104017f;       (* arm_CMP X11 (rvalue (word 256)) *)
  0x54fffe4b;       (* arm_BLT (word 2097096) *)
  0xaa0903e0;       (* arm_MOV X0 X9 *)
  0x910903ff;       (* arm_ADD SP SP (rvalue (word 576)) *)
  0xd65f03c0        (* arm_RET X30 *)
];;
(*** BYTECODE END ***)

let MLDSA_REJ_UNIFORM_ETA4_EXEC = ARM_MK_EXEC_RULE mldsa_rej_uniform_eta4_mc;;

let LENGTH_MLDSA_REJ_UNIFORM_ETA4_MC =
  REWRITE_CONV[mldsa_rej_uniform_eta4_mc] `LENGTH mldsa_rej_uniform_eta4_mc`
  |> CONV_RULE (RAND_CONV LENGTH_CONV);;

(* Nibble extraction *)
let NIBBLE_PAIR = define
  `NIBBLE_PAIR (b:byte) =
   [word(val b MOD 16):int16; word(val b DIV 16):int16]`;;

let NIBBLES_OF_BYTES = define
  `NIBBLES_OF_BYTES [] = ([]:(int16)list) /\
   NIBBLES_OF_BYTES (CONS (b:byte) t) =
   APPEND (NIBBLE_PAIR b) (NIBBLES_OF_BYTES t)`;;

let NIBBLES_OF_BYTES_APPEND = prove
 (`!l1 l2. NIBBLES_OF_BYTES(APPEND l1 l2) =
           APPEND (NIBBLES_OF_BYTES l1) (NIBBLES_OF_BYTES l2)`,
  LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[NIBBLES_OF_BYTES; APPEND; APPEND_ASSOC]);;

(* Rejection sampling spec *)
let REJ_NIBBLES_ETA4 = define
  `REJ_NIBBLES_ETA4 l =
   FILTER (\x:int16. val x < 9) (NIBBLES_OF_BYTES l)`;;

let REJ_SAMPLE_ETA4 = define
  `REJ_SAMPLE_ETA4 l =
   MAP (\x:int16. word_sx(word_sub (word 4:int16) x):int32)
       (REJ_NIBBLES_ETA4 l)`;;

let REJ_NIBBLES_ETA4_EMPTY = prove
 (`REJ_NIBBLES_ETA4 [] = []`,
  REWRITE_TAC[REJ_NIBBLES_ETA4; NIBBLES_OF_BYTES; FILTER]);;

let REJ_SAMPLE_ETA4_EMPTY = prove
 (`REJ_SAMPLE_ETA4 [] = []`,
  REWRITE_TAC[REJ_SAMPLE_ETA4; REJ_NIBBLES_ETA4_EMPTY; MAP]);;

let REJ_NIBBLES_ETA4_APPEND = prove
 (`!l1 l2. REJ_NIBBLES_ETA4(APPEND l1 l2) =
           APPEND (REJ_NIBBLES_ETA4 l1) (REJ_NIBBLES_ETA4 l2)`,
  REWRITE_TAC[REJ_NIBBLES_ETA4; NIBBLES_OF_BYTES_APPEND; FILTER_APPEND]);;

let REJ_NIBBLES_ETA4_STEP = prove
 (`!inlist:byte list. !i:num.
   8 * (i + 1) <= LENGTH inlist
   ==> REJ_NIBBLES_ETA4(SUB_LIST(0, 8 * (i + 1)) inlist) =
       APPEND (REJ_NIBBLES_ETA4(SUB_LIST(0, 8 * i) inlist))
              (REJ_NIBBLES_ETA4(SUB_LIST(8 * i, 8) inlist))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM REJ_NIBBLES_ETA4_APPEND] THEN
  AP_TERM_TAC THEN
  SUBGOAL_THEN `8 * (i + 1) = 0 + 8 * i + 8` SUBST1_TAC THENL
   [ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[SUB_LIST_SPLIT; SUB_LIST_CLAUSES; APPEND; ADD_CLAUSES]);;

let REJ_SAMPLE_ETA4_APPEND = prove
 (`!l1 l2. REJ_SAMPLE_ETA4(APPEND l1 l2) =
           APPEND (REJ_SAMPLE_ETA4 l1) (REJ_SAMPLE_ETA4 l2)`,
  REWRITE_TAC[REJ_SAMPLE_ETA4; REJ_NIBBLES_ETA4_APPEND; MAP_APPEND]);;

let LENGTH_FILTER = prove
 (`!P l:A list. LENGTH(FILTER P l) <= LENGTH l`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[FILTER; LE_REFL] THEN
  COND_CASES_TAC THEN REWRITE_TAC[LENGTH] THEN ASM_ARITH_TAC);;

let LENGTH_REJ_NIBBLES_ETA4 = prove
 (`!l:byte list. LENGTH(REJ_NIBBLES_ETA4 l) <= 2 * LENGTH l`,
  GEN_TAC THEN REWRITE_TAC[REJ_NIBBLES_ETA4] THEN
  TRANS_TAC LE_TRANS `LENGTH(NIBBLES_OF_BYTES l:int16 list)` THEN
  CONJ_TAC THENL [REWRITE_TAC[LENGTH_FILTER]; ALL_TAC] THEN
  SPEC_TAC(`l:byte list`,`l:byte list`) THEN
  LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[NIBBLES_OF_BYTES; LENGTH; NIBBLE_PAIR;
                  APPEND; LENGTH_APPEND; LE_0] THEN
  UNDISCH_TAC `LENGTH(NIBBLES_OF_BYTES t:int16 list) <=
               2 * LENGTH(t:byte list)` THEN ARITH_TAC);;

(* Helper lemma *)
let EIGHT_N_LE_BUFLEN = prove
 (`(!m. m < N ==> ~(buflen < 8 * (m + 1))) /\ 0 < N
   ==> 8 * N <= buflen`,
  STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `N - 1`) THEN
  ASM_REWRITE_TAC[ARITH_RULE `N - 1 < N <=> 0 < N`] THEN ARITH_TAC);;

(* Q31 word_insert simplification *)
let WORD_INSERT_Q31 = prove(
  `word_insert ((word_insert:int128->num#num->int64->int128) q (0,64)
    (word 2251816993685505)) (64,64) (word 36029071898968080:int64) =
    (word 664619068533544770747334646890102785:int128)`,
  CONV_TAC WORD_BLAST);;

(* ========================================================================= *)
(* Additional helpers (from rej_uniform proof pattern)                       *)
(* ========================================================================= *)

let DIMINDEX_16 = DIMINDEX_CONV `dimindex(:16)`;;

(* ========================================================================= *)
(* WORD_ADD_SHL1 lemma for X7 pointer arithmetic in loop body               *)
(* ========================================================================= *)

let WORD_ADD_SHL1 = WORD_BLAST
 `!sp (x:int64) k.
    word_add (word_add sp (word(2 * k):int64))
             (word_shl x 1:int64) =
    word_add sp (word(2 * (k + val(x:int64))):int64)`;;

(* ========================================================================= *)
(* USHLL halfword extraction: each halfword of the USHLL output equals       *)
(* the zero-extended corresponding byte of the input.                        *)
(* Used to connect SIMD nibble extraction to NIBBLES_OF_BYTES.               *)
(* ========================================================================= *)

let USHLL_HALFWORDS = map (fun k ->
  let ks = string_of_int(16*k) and bs = string_of_int(8*k) in
  BITBLAST_RULE(parse_term(
    "word_subword (word_join (word_join " ^
    "(word_join (word_zx(word_subword (d:int64) (56,8):byte):int16) " ^
    "(word_zx(word_subword d (48,8):byte):int16):int32) " ^
    "(word_join (word_zx(word_subword d (40,8):byte):int16) " ^
    "(word_zx(word_subword d (32,8):byte):int16):int32):int64) " ^
    "(word_join (word_join (word_zx(word_subword d (24,8):byte):int16) " ^
    "(word_zx(word_subword d (16,8):byte):int16):int32) " ^
    "(word_join (word_zx(word_subword d (8,8):byte):int16) " ^
    "(word_zx(word_subword d (0,8):byte):int16):int32):int64):int128) " ^
    "(" ^ ks ^ ",16):int16 = word_zx(word_subword d (" ^ bs ^ ",8):byte)")))
  (0--7);;

(* ========================================================================= *)
(* Popcount lemmas for proving val(X12) <= 8 and val(X13) <= 8              *)
(* Q31 = 0x0080_0040_0020_0010__0008_0004_0002_0001: one bit per halfword   *)
(* So word_and y Q31 has at most 1 bit per halfword, CNT+UADDLV <= 8        *)
(* ========================================================================= *)

let POPCOUNT_AND_POWERS = BITBLAST_RULE
  `word_popcount(word_and (word 1) x:byte) = bitval(bit 0 x) /\
   word_popcount(word_and (word 2) x:byte) = bitval(bit 1 x) /\
   word_popcount(word_and (word 4) x:byte) = bitval(bit 2 x) /\
   word_popcount(word_and (word 8) x:byte) = bitval(bit 3 x) /\
   word_popcount(word_and (word 16) x:byte) = bitval(bit 4 x) /\
   word_popcount(word_and (word 32) x:byte) = bitval(bit 5 x) /\
   word_popcount(word_and (word 64) x:byte) = bitval(bit 6 x) /\
   word_popcount(word_and (word 128) x:byte) = bitval(bit 7 x)`;;

let BITVAL_BOUND = prove(`!b. bitval b <= 1`,
  BOOL_CASES_TAC `b:bool` THEN REWRITE_TAC[bitval] THEN ARITH_TAC);;

let WJ0_VAL = WORD_BLAST
  `val(word_join (word 0:byte) (x:byte):int16) = val x`;;

let BITVAL_MOD256 = prove(`!b. bitval b MOD 256 = bitval b`,
  GEN_TAC THEN BOOL_CASES_TAC `b:bool` THEN
  REWRITE_TAC[bitval] THEN CONV_TAC NUM_REDUCE_CONV);;

let BITVAL_MOD65536 = prove(`!b. bitval b MOD 65536 = bitval b`,
  GEN_TAC THEN BOOL_CASES_TAC `b:bool` THEN
  REWRITE_TAC[bitval] THEN CONV_TAC NUM_REDUCE_CONV);;

(* UADDLV bound: val of the full UADDLV word expression with 8 bitvals <= 8 *)
let UADDLV_BOUND_LEMMA = prove
 (`!b0 b1 b2 b3 b4 b5 b6 b7.
   val(word_zx(word_subword
     (word_add (word_subword(word_join (word 0:byte) (word(bitval b0):byte):int16)(0,16):int128)
     (word_add (word_subword(word_join (word 0:byte) (word(bitval b1):byte):int16)(0,16):int128)
     (word_add (word_subword(word_join (word 0:byte) (word(bitval b2):byte):int16)(0,16):int128)
     (word_add (word_subword(word_join (word 0:byte) (word(bitval b3):byte):int16)(0,16):int128)
     (word_add (word_subword(word_join (word 0:byte) (word(bitval b4):byte):int16)(0,16):int128)
     (word_add (word_subword(word_join (word 0:byte) (word(bitval b5):byte):int16)(0,16):int128)
     (word_add (word_subword(word_join (word 0:byte) (word(bitval b6):byte):int16)(0,16):int128)
     (word_subword(word_join (word 0:byte) (word(bitval b7):byte):int16)(0,16):int128))))))))(0,32):int32):int64) <= 8`,
  REPEAT GEN_TAC THEN
  MAP_EVERY BOOL_CASES_TAC [`b0:bool`;`b1:bool`;`b2:bool`;`b3:bool`;
    `b4:bool`;`b5:bool`;`b6:bool`;`b7:bool`] THEN
  REWRITE_TAC[bitval] THEN CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV));;

let cnt_hw_tac =
  GEN_TAC THEN REWRITE_TAC[WORD_SUBWORD_AND] THEN
  CONV_TAC(DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
  CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV) THEN
  REWRITE_TAC[WORD_AND_0; WORD_POPCOUNT_0; ADD_CLAUSES] THEN
  ONCE_REWRITE_TAC[WORD_AND_SYM] THEN
  REWRITE_TAC[POPCOUNT_AND_POWERS; BITVAL_BOUND];;

(* FILTER length = sum of bitvals for 8 elements *)
let FILTER_LENGTH_BITVAL = prove(
  `!a b c d e f g h:int16.
   LENGTH(FILTER (\x:int16. val x < 9) [a;b;c;d;e;f;g;h]) =
   bitval(val a < 9) + bitval(val b < 9) + bitval(val c < 9) +
   bitval(val d < 9) + bitval(val e < 9) + bitval(val f < 9) +
   bitval(val g < 9) + bitval(val h < 9)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[FILTER] THEN
  REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[LENGTH; bitval]) THEN
  ARITH_TAC);;

(* Exact UADDLV value = sum of bitvals (not just bound) *)
let UADDLV_COUNT_LEMMA = prove
 (`!b0 b1 b2 b3 b4 b5 b6 b7.
   val(word_zx(word_subword
     (word_add (word_subword(word_join (word 0:byte) (word(bitval b0):byte):int16)(0,16):int128)
     (word_add (word_subword(word_join (word 0:byte) (word(bitval b1):byte):int16)(0,16):int128)
     (word_add (word_subword(word_join (word 0:byte) (word(bitval b2):byte):int16)(0,16):int128)
     (word_add (word_subword(word_join (word 0:byte) (word(bitval b3):byte):int16)(0,16):int128)
     (word_add (word_subword(word_join (word 0:byte) (word(bitval b4):byte):int16)(0,16):int128)
     (word_add (word_subword(word_join (word 0:byte) (word(bitval b5):byte):int16)(0,16):int128)
     (word_add (word_subword(word_join (word 0:byte) (word(bitval b6):byte):int16)(0,16):int128)
     (word_subword(word_join (word 0:byte) (word(bitval b7):byte):int16)(0,16):int128))))))))(0,32):int32):int64) =
   bitval b0 + bitval b1 + bitval b2 + bitval b3 +
   bitval b4 + bitval b5 + bitval b6 + bitval b7`,
  REPEAT GEN_TAC THEN
  MAP_EVERY BOOL_CASES_TAC [`b0:bool`;`b1:bool`;`b2:bool`;`b3:bool`;
    `b4:bool`;`b5:bool`;`b6:bool`;`b7:bool`] THEN
  REWRITE_TAC[bitval] THEN CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV));;

let CNT_HW_BOUNDS = map (fun k ->
  let lo = string_of_int (k * 16) and hi = string_of_int (k * 16 + 8) in
  prove(parse_term(
    "!y:int128. word_popcount(word_subword (word_and y " ^
    "(word 664619068533544770747334646890102785:int128)) (" ^ lo ^ ",8):byte) + " ^
    "word_popcount(word_subword (word_and y " ^
    "(word 664619068533544770747334646890102785:int128)) (" ^ hi ^ ",8):byte) <= 1"),
    cnt_hw_tac)) (0--7);;

let CNT_UADDLV_BOUND = prove(
 `!y:int128.
   word_popcount(word_subword (word_and y (word 664619068533544770747334646890102785:int128)) (0,8):byte) +
   word_popcount(word_subword (word_and y (word 664619068533544770747334646890102785:int128)) (8,8):byte) +
   word_popcount(word_subword (word_and y (word 664619068533544770747334646890102785:int128)) (16,8):byte) +
   word_popcount(word_subword (word_and y (word 664619068533544770747334646890102785:int128)) (24,8):byte) +
   word_popcount(word_subword (word_and y (word 664619068533544770747334646890102785:int128)) (32,8):byte) +
   word_popcount(word_subword (word_and y (word 664619068533544770747334646890102785:int128)) (40,8):byte) +
   word_popcount(word_subword (word_and y (word 664619068533544770747334646890102785:int128)) (48,8):byte) +
   word_popcount(word_subword (word_and y (word 664619068533544770747334646890102785:int128)) (56,8):byte) +
   word_popcount(word_subword (word_and y (word 664619068533544770747334646890102785:int128)) (64,8):byte) +
   word_popcount(word_subword (word_and y (word 664619068533544770747334646890102785:int128)) (72,8):byte) +
   word_popcount(word_subword (word_and y (word 664619068533544770747334646890102785:int128)) (80,8):byte) +
   word_popcount(word_subword (word_and y (word 664619068533544770747334646890102785:int128)) (88,8):byte) +
   word_popcount(word_subword (word_and y (word 664619068533544770747334646890102785:int128)) (96,8):byte) +
   word_popcount(word_subword (word_and y (word 664619068533544770747334646890102785:int128)) (104,8):byte) +
   word_popcount(word_subword (word_and y (word 664619068533544770747334646890102785:int128)) (112,8):byte) +
   word_popcount(word_subword (word_and y (word 664619068533544770747334646890102785:int128)) (120,8):byte) <= 8`,
 GEN_TAC THEN
 MAP_EVERY (fun th -> MP_TAC(SPEC `y:int128` th)) CNT_HW_BOUNDS THEN
 ARITH_TAC);;

(* Writeback lemmas: word_sx(word_sub(word 4) x) = word_sub(word 4)(word_zx x) *)
(* for nibbles with val < 9 (the only values produced by REJ_NIBBLES_ETA4).   *)

let WORD_SX_SUB4_SMALL = BITBLAST_RULE
  `val(x:int16) < 9
   ==> word_sx(word_sub (word 4:int16) x):int32 =
       word_sub (word 4) (word_zx x)`;;

let ALL_REJ_NIBBLES_ETA4 = prove(
  `!l. ALL (\x. val(x:int16) < 9) (REJ_NIBBLES_ETA4 l)`,
  GEN_TAC THEN REWRITE_TAC[REJ_NIBBLES_ETA4; GSYM ALL_MEM; MEM_FILTER] THEN
  SIMP_TAC[]);;

let SUB_LIST_MAP = prove(
  `!f (l:A list) n.
     SUB_LIST(0,n)(MAP f l) = MAP f (SUB_LIST(0,n) l):B list`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN INDUCT_TAC THEN
  ASM_REWRITE_TAC[MAP; SUB_LIST_CLAUSES]);;

let SSHLL_LOWER = BITBLAST_RULE
  `word_join
   (word_join
    (word_shl (word_sx (word_subword (word_subword (q:int128) (0,64):int64)
                                     (48,16):int16):int32) 0)
    (word_shl (word_sx (word_subword (word_subword q (0,64):int64)
                                     (32,16):int16):int32) 0):int64)
   (word_join
    (word_shl (word_sx (word_subword (word_subword q (0,64):int64)
                                     (16,16):int16):int32) 0)
    (word_shl (word_sx (word_subword (word_subword q (0,64):int64)
                                     (0,16):int16):int32) 0):int64):int128 =
   word_join
   (word_join (word_sx (word_subword q (48,16):int16):int32)
              (word_sx (word_subword q (32,16):int16):int32):int64)
   (word_join (word_sx (word_subword q (16,16):int16):int32)
              (word_sx (word_subword q (0,16):int16):int32):int64):int128`;;

let SSHLL_UPPER = BITBLAST_RULE
  `word_join
   (word_join
    (word_shl (word_sx (word_subword (word_subword (q:int128) (64,64):int64)
                                     (48,16):int16):int32) 0)
    (word_shl (word_sx (word_subword (word_subword q (64,64):int64)
                                     (32,16):int16):int32) 0):int64)
   (word_join
    (word_shl (word_sx (word_subword (word_subword q (64,64):int64)
                                     (16,16):int16):int32) 0)
    (word_shl (word_sx (word_subword (word_subword q (64,64):int64)
                                     (0,16):int16):int32) 0):int64):int128 =
   word_join
   (word_join (word_sx (word_subword q (112,16):int16):int32)
              (word_sx (word_subword q (96,16):int16):int32):int64)
   (word_join (word_sx (word_subword q (80,16):int16):int32)
              (word_sx (word_subword q (64,16):int16):int32):int64):int128`;;

(* Per-iteration writeback block identities: the ARM output bytes128       *)
(* (with packed SUB vector + word_sx extraction) equals the clean form      *)
(* with direct word_sx(word_sub(word 4)(word_subword q (k,16))).            *)
(* These reduce the 366K-char ARM output to 47K chars after rewriting.      *)

let WB_BLOCK_LO = BITBLAST_RULE
 `word_join (word_join
    (word_sx (word_subword (word_join (word_join (word_join
       (word_sub (word 4:int16) (word_subword (q:int128) (112,16):int16):int16)
       (word_sub (word 4:int16) (word_subword q (96,16):int16):int16):int32)
      (word_join (word_sub (word 4:int16) (word_subword q (80,16):int16):int16)
       (word_sub (word 4:int16) (word_subword q (64,16):int16):int16):int32):int64)
     (word_join (word_join
       (word_sub (word 4:int16) (word_subword q (48,16):int16):int16)
       (word_sub (word 4:int16) (word_subword q (32,16):int16):int16):int32)
      (word_join (word_sub (word 4:int16) (word_subword q (16,16):int16):int16)
       (word_sub (word 4:int16) (word_subword q (0,16):int16):int16):int32):int64)
     :int128) (48,16):int16):int32)
    (word_sx (word_subword (word_join (word_join (word_join
       (word_sub (word 4:int16) (word_subword q (112,16):int16):int16)
       (word_sub (word 4:int16) (word_subword q (96,16):int16):int16):int32)
      (word_join (word_sub (word 4:int16) (word_subword q (80,16):int16):int16)
       (word_sub (word 4:int16) (word_subword q (64,16):int16):int16):int32):int64)
     (word_join (word_join
       (word_sub (word 4:int16) (word_subword q (48,16):int16):int16)
       (word_sub (word 4:int16) (word_subword q (32,16):int16):int16):int32)
      (word_join (word_sub (word 4:int16) (word_subword q (16,16):int16):int16)
       (word_sub (word 4:int16) (word_subword q (0,16):int16):int16):int32):int64)
     :int128) (32,16):int16):int32):int64)
   (word_join
    (word_sx (word_subword (word_join (word_join (word_join
       (word_sub (word 4:int16) (word_subword q (112,16):int16):int16)
       (word_sub (word 4:int16) (word_subword q (96,16):int16):int16):int32)
      (word_join (word_sub (word 4:int16) (word_subword q (80,16):int16):int16)
       (word_sub (word 4:int16) (word_subword q (64,16):int16):int16):int32):int64)
     (word_join (word_join
       (word_sub (word 4:int16) (word_subword q (48,16):int16):int16)
       (word_sub (word 4:int16) (word_subword q (32,16):int16):int16):int32)
      (word_join (word_sub (word 4:int16) (word_subword q (16,16):int16):int16)
       (word_sub (word 4:int16) (word_subword q (0,16):int16):int16):int32):int64)
     :int128) (16,16):int16):int32)
    (word_sx (word_subword (word_join (word_join (word_join
       (word_sub (word 4:int16) (word_subword q (112,16):int16):int16)
       (word_sub (word 4:int16) (word_subword q (96,16):int16):int16):int32)
      (word_join (word_sub (word 4:int16) (word_subword q (80,16):int16):int16)
       (word_sub (word 4:int16) (word_subword q (64,16):int16):int16):int32):int64)
     (word_join (word_join
       (word_sub (word 4:int16) (word_subword q (48,16):int16):int16)
       (word_sub (word 4:int16) (word_subword q (32,16):int16):int16):int32)
      (word_join (word_sub (word 4:int16) (word_subword q (16,16):int16):int16)
       (word_sub (word 4:int16) (word_subword q (0,16):int16):int16):int32):int64)
     :int128) (0,16):int16):int32):int64):int128
  = word_join
     (word_join (word_sx(word_sub (word 4:int16) (word_subword q (48,16):int16)):int32)
                (word_sx(word_sub (word 4:int16) (word_subword q (32,16):int16)):int32):int64)
     (word_join (word_sx(word_sub (word 4:int16) (word_subword q (16,16):int16)):int32)
                (word_sx(word_sub (word 4:int16) (word_subword q (0,16):int16)):int32):int64)
     :int128`;;

let WB_BLOCK_HI = BITBLAST_RULE
 `word_join (word_join
    (word_sx (word_subword (word_join (word_join (word_join
       (word_sub (word 4:int16) (word_subword (q:int128) (112,16):int16):int16)
       (word_sub (word 4:int16) (word_subword q (96,16):int16):int16):int32)
      (word_join (word_sub (word 4:int16) (word_subword q (80,16):int16):int16)
       (word_sub (word 4:int16) (word_subword q (64,16):int16):int16):int32):int64)
     (word_join (word_join
       (word_sub (word 4:int16) (word_subword q (48,16):int16):int16)
       (word_sub (word 4:int16) (word_subword q (32,16):int16):int16):int32)
      (word_join (word_sub (word 4:int16) (word_subword q (16,16):int16):int16)
       (word_sub (word 4:int16) (word_subword q (0,16):int16):int16):int32):int64)
     :int128) (112,16):int16):int32)
    (word_sx (word_subword (word_join (word_join (word_join
       (word_sub (word 4:int16) (word_subword q (112,16):int16):int16)
       (word_sub (word 4:int16) (word_subword q (96,16):int16):int16):int32)
      (word_join (word_sub (word 4:int16) (word_subword q (80,16):int16):int16)
       (word_sub (word 4:int16) (word_subword q (64,16):int16):int16):int32):int64)
     (word_join (word_join
       (word_sub (word 4:int16) (word_subword q (48,16):int16):int16)
       (word_sub (word 4:int16) (word_subword q (32,16):int16):int16):int32)
      (word_join (word_sub (word 4:int16) (word_subword q (16,16):int16):int16)
       (word_sub (word 4:int16) (word_subword q (0,16):int16):int16):int32):int64)
     :int128) (96,16):int16):int32):int64)
   (word_join
    (word_sx (word_subword (word_join (word_join (word_join
       (word_sub (word 4:int16) (word_subword q (112,16):int16):int16)
       (word_sub (word 4:int16) (word_subword q (96,16):int16):int16):int32)
      (word_join (word_sub (word 4:int16) (word_subword q (80,16):int16):int16)
       (word_sub (word 4:int16) (word_subword q (64,16):int16):int16):int32):int64)
     (word_join (word_join
       (word_sub (word 4:int16) (word_subword q (48,16):int16):int16)
       (word_sub (word 4:int16) (word_subword q (32,16):int16):int16):int32)
      (word_join (word_sub (word 4:int16) (word_subword q (16,16):int16):int16)
       (word_sub (word 4:int16) (word_subword q (0,16):int16):int16):int32):int64)
     :int128) (80,16):int16):int32)
    (word_sx (word_subword (word_join (word_join (word_join
       (word_sub (word 4:int16) (word_subword q (112,16):int16):int16)
       (word_sub (word 4:int16) (word_subword q (96,16):int16):int16):int32)
      (word_join (word_sub (word 4:int16) (word_subword q (80,16):int16):int16)
       (word_sub (word 4:int16) (word_subword q (64,16):int16):int16):int32):int64)
     (word_join (word_join
       (word_sub (word 4:int16) (word_subword q (48,16):int16):int16)
       (word_sub (word 4:int16) (word_subword q (32,16):int16):int16):int32)
      (word_join (word_sub (word 4:int16) (word_subword q (16,16):int16):int16)
       (word_sub (word 4:int16) (word_subword q (0,16):int16):int16):int32):int64)
     :int128) (64,16):int16):int32):int64):int128
  = word_join
     (word_join (word_sx(word_sub (word 4:int16) (word_subword q (112,16):int16)):int32)
                (word_sx(word_sub (word 4:int16) (word_subword q (96,16):int16)):int32):int64)
     (word_join (word_sx(word_sub (word 4:int16) (word_subword q (80,16):int16)):int32)
                (word_sx(word_sub (word 4:int16) (word_subword q (64,16):int16)):int32):int64)
     :int128`;;

(* ========================================================================= *)
(* The proof (interactive g/e style).                                        *)
(* Run each e(...) in sequence in a HOL Light session with the checkpoint.   *)
(* ========================================================================= *)

set_goal([], `!res buf buflen table (inlist:byte list) pc stackpointer.
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
                       memory :> bytes(stackpointer,576)])`);;

(* === FULL PROOF TACTIC (with 3 CHEATs) === *)
(* Takes ~60 seconds total *)
(* Key technique: ENSURES_SEQUENCE_TAC within loop body at pc+0xD8 *)
(* to capture X12/X13 bounds before ST1 stores.                   *)
(* ARM_VERBOSE_STEP_TAC for FMOV exposes symbolic X12/X13.        *)

e (REWRITE_TAC[LENGTH_MLDSA_REJ_UNIFORM_ETA4_MC;
    fst MLDSA_REJ_UNIFORM_ETA4_EXEC;
    MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI;
    C_ARGUMENTS; ALL; C_RETURN] THEN
 MAP_EVERY X_GEN_TAC [`res:int64`; `buf:int64`] THEN
 W64_GEN_TAC `buflen:num` THEN
 MAP_EVERY X_GEN_TAC
  [`table:int64`; `inlist:byte list`; `pc:num`; `stackpointer:int64`] THEN
 DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN

 (* === Split: computation (pc+4 to pc+256) and writeback (to pc+336) === *)
 (* Intermediate postcondition at pc+256 (CMP X9,X4 instruction) tracks   *)
 (* REJ_NIBBLES_ETA4(inlist) directly -- no existential, no niblen bound. *)
 (* Loop uses buflen DIV 8 iterations: exhausts entire buffer, BCS        *)
 (* deterministically not taken after last iteration.                      *)
 ENSURES_SEQUENCE_TAC `pc + 256`
  `\s. aligned_bytes_loaded s (word pc) mldsa_rej_uniform_eta4_mc /\
       read PC s = word(pc + 256) /\
       read X0 s = res /\ read X4 s = word 256 /\
       read X8 s = stackpointer /\
       read Q7 s = word 20769504351625144638033088116686852 /\
       ALL (nonoverlapping (res,1024)) [(word pc,344); (stackpointer,576)] /\
       let niblist = REJ_NIBBLES_ETA4 inlist in
       let niblen = LENGTH niblist in
       read X9 s = word niblen /\
       read (memory :> bytes (stackpointer,2 * niblen)) s =
       num_of_wordlist niblist` THEN
 CONJ_TAC THENL
  [ALL_TAC;

   (*** Writeback phase: pc+256 to pc+336 ***)
   (*** Unroll the writeback loop: 245 ARM steps ***)
   ENSURES_INIT_TAC "s0" THEN
   CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
   ABBREV_TAC `niblist = REJ_NIBBLES_ETA4 (inlist:byte list):int16 list` THEN
   ABBREV_TAC `niblen = LENGTH(niblist:int16 list)` THEN
   DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
   VAL_INT64_TAC `niblen:num` THEN
   BIGNUM_LDIGITIZE_TAC "b_"
     `read (memory :> bytes(stackpointer,8 * 64)) s0` THEN
   MEMORY_128_FROM_64_TAC "stackpointer" 0 32 THEN
   ASM_REWRITE_TAC[WORD_ADD_0] THEN STRIP_TAC THEN
   ARM_STEPS_TAC MLDSA_REJ_UNIFORM_ETA4_EXEC (1--245) THEN
   ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
   CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
   SUBGOAL_THEN `LENGTH(REJ_SAMPLE_ETA4 inlist:int32 list) = niblen`
   ASSUME_TAC THENL
    [REWRITE_TAC[REJ_SAMPLE_ETA4; LENGTH_MAP] THEN
     FIRST_X_ASSUM(fun th -> REWRITE_TAC[SYM th]) THEN
     ASM_REWRITE_TAC[]; ALL_TAC] THEN
   ASM_REWRITE_TAC[LENGTH_SUB_LIST; SUB_0] THEN
   GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [GSYM COND_RAND] THEN
   REWRITE_TAC[ARITH_RULE `(if l < p then l else p) = MIN p l`] THEN
   CONJ_TAC THENL [REFL_TAC; ALL_TAC] THEN
   CHEAT_TAC] THEN  (* CHEAT: writeback memory content *)

 (* === Loop with buflen DIV 8 iterations === *)
 SUBGOAL_THEN `0 < buflen DIV 8` ASSUME_TAC THENL
  [MP_TAC(ASSUME `8 <= buflen`) THEN ARITH_TAC; ALL_TAC] THEN

 ENSURES_WHILE_UP_TAC `buflen DIV 8` `pc + 108` `pc + 248`
  `\i s. read (memory :> bytes (table,4096)) s =
         num_of_wordlist mldsa_rej_uniform_eta_table /\
         read (memory :> bytes (buf,buflen)) s = num_of_wordlist inlist /\
         aligned_bytes_loaded s (word pc) mldsa_rej_uniform_eta4_mc /\
         read Q7 s = word 20769504351625144638033088116686852 /\
         read Q30 s = word 46731384791156575435574448262545417 /\
         read Q31 s = word 664619068533544770747334646890102785 /\
         let niblist = REJ_NIBBLES_ETA4(SUB_LIST(0,8 * i) inlist) in
         let niblen = LENGTH niblist in
         niblen < 272 /\
         read X0 s = res /\
         read X1 s = word_add buf (word(8 * i)) /\
         read X2 s = word_sub (word buflen) (word(8 * i)) /\
         read X3 s = table /\ read X4 s = word 256 /\
         read X7 s = word_add stackpointer (word(2 * niblen)) /\
         read X8 s = stackpointer /\ read X9 s = word niblen /\
         read (memory :> bytes (stackpointer,2 * niblen)) s =
         num_of_wordlist niblist` THEN
 REPEAT CONJ_TAC THENL
  [(*** Subgoal 1: 0 < buflen DIV 8 ***)
   ASM_ARITH_TAC;

   (*** Subgoal 2: Pre-loop init (75 ARM steps) ***)
   GHOST_INTRO_TAC `q31_init:int128` `read Q31` THEN
   ENSURES_INIT_TAC "s0" THEN
   ARM_STEPS_TAC MLDSA_REJ_UNIFORM_ETA4_EXEC (1--75) THEN
   ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
   CONJ_TAC THENL [REWRITE_TAC[WORD_INSERT_Q31]; ALL_TAC] THEN
   REWRITE_TAC[MULT_CLAUSES; SUB_LIST_CLAUSES; REJ_NIBBLES_ETA4_EMPTY] THEN
   CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REWRITE_TAC[LENGTH] THEN
   REWRITE_TAC[MULT_CLAUSES; WORD_ADD_0; WORD_SUB_0] THEN
   CONV_TAC NUM_REDUCE_CONV THEN
   REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_TRIVIAL; num_of_wordlist];

   (*** Subgoal 3: Loop body — split at pc+0xD8 for ST1 stores ***)
   X_GEN_TAC `i:num` THEN STRIP_TAC THEN
   ABBREV_TAC `curlist = REJ_NIBBLES_ETA4(SUB_LIST(0,8 * i) inlist)` THEN
   ABBREV_TAC `curlen = LENGTH(curlist:int16 list)` THEN
   CONV_TAC(RATOR_CONV(LAND_CONV(TOP_DEPTH_CONV let_CONV))) THEN
   ASM_REWRITE_TAC[] THEN
   ENSURES_INIT_TAC "s0" THEN
   (* Split loop body: first half = SIMD compute, second half = stores *)
   ENSURES_SEQUENCE_TAC `pc + 0xe0`
    `\s. read (memory :> bytes (table,4096)) s =
         num_of_wordlist mldsa_rej_uniform_eta_table /\
         read (memory :> bytes (buf,buflen)) s = num_of_wordlist (inlist:byte list) /\
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
         num_of_wordlist (curlist:int16 list) /\
         val(read X12 s:int64) <= 8 /\
         val(read X13 s:int64) <= 8 /\
         val(read X12 s:int64) + val(read X13 s:int64) =
         LENGTH(REJ_NIBBLES_ETA4(SUB_LIST(8 * i,8) inlist):int16 list) /\
         curlen < 256 /\
         nonoverlapping (stackpointer,576) (word pc,344)` THEN
   CONJ_TAC THENL
    [(* First half: SIMD compute chain *)
     GHOST_INTRO_TAC `nibbles1:int128` `read Q17` THEN
     ENSURES_INIT_TAC "s0" THEN
     ARM_STEPS_TAC MLDSA_REJ_UNIFORM_ETA4_EXEC (1--2) THEN
     SUBGOAL_THEN `~(256 <= val(word curlen:int64))` ASSUME_TAC THENL
      [VAL_INT64_TAC `curlen:num` THEN ASM_REWRITE_TAC[] THEN
       ASM_ARITH_TAC; ALL_TAC] THEN
     RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `~(256 <= val(word curlen:int64))`]) THEN
     (* Steps 3-11: nibble extraction through USHLL *)
     ARM_STEPS_TAC MLDSA_REJ_UNIFORM_ETA4_EXEC (3--11) THEN
     (* ABBREV Q16/Q17 to preserve through later steps *)
     ABBREV_TAC `nibbles0:int128 = read Q16 s11` THEN
     ABBREV_TAC `nibbles1b:int128 = read Q17 s11` THEN
     (* Steps 12-29: CMHI through TBL *)
     ARM_STEPS_TAC MLDSA_REJ_UNIFORM_ETA4_EXEC (12--19) THEN
     RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV)) THEN
     RULE_ASSUM_TAC(CONV_RULE WORD_REDUCE_CONV) THEN
     RULE_ASSUM_TAC(REWRITE_RULE
      [word_ugt; relational2; GT; WORD_AND_MASK]) THEN
     RULE_ASSUM_TAC(ONCE_REWRITE_RULE[COND_RAND]) THEN
     RULE_ASSUM_TAC(CONV_RULE WORD_REDUCE_CONV) THEN
     (* No REABBREV for idx — let full expression flow for COND_CASES *)
     ARM_STEPS_TAC MLDSA_REJ_UNIFORM_ETA4_EXEC (20--25) THEN
     RULE_ASSUM_TAC(REWRITE_RULE[WORD_SUBWORD_AND]) THEN
     RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV)) THEN
     RULE_ASSUM_TAC(CONV_RULE WORD_REDUCE_CONV) THEN
     RULE_ASSUM_TAC(REWRITE_RULE
      [word_ugt; relational2; GT; WORD_AND_MASK]) THEN
     RULE_ASSUM_TAC(ONCE_REWRITE_RULE[COND_RAND]) THEN
     RULE_ASSUM_TAC(CONV_RULE WORD_REDUCE_CONV) THEN
     ARM_STEPS_TAC MLDSA_REJ_UNIFORM_ETA4_EXEC (26--29) THEN
     ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
     ASM_REWRITE_TAC[WORD_SUBWORD_AND] THEN
     CONV_TAC(DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
     CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV) THEN
     REWRITE_TAC[WORD_AND_0; WORD_POPCOUNT_0; ADD_CLAUSES] THEN
     REWRITE_TAC[POPCOUNT_AND_POWERS] THEN
     REPEAT CONJ_TAC THEN
     TRY(CONV_TAC WORD_RULE) THEN
     TRY(NONOVERLAPPING_TAC) THEN
     TRY(REWRITE_TAC[UADDLV_BOUND_LEMMA] THEN NO_TAC) THEN
     TRY(REWRITE_TAC[UADDLV_COUNT_LEMMA] THEN
         REWRITE_TAC(List.map (fun k -> BITBLAST_RULE
           (vsubst [mk_small_numeral k, `k:num`]
           `bit k (word_subword (word_neg (word (bitval b):16 word))
                   (0,8):8 word) <=> b`)) (0--7)) THEN
         ASM_REWRITE_TAC[] THEN
         CHEAT_TAC) THEN  (* CHEAT: 16 bitvals = LENGTH(REJ_NIBBLES_ETA4...) *)
     ASM_ARITH_TAC;
     ALL_TAC] THEN
   (* Second half: ST1 + ADD + count accumulation + CMP *)
   ENSURES_INIT_TAC "s0" THEN
   ABBREV_TAC `len0 = val(read X12 s0:int64)` THEN
   ABBREV_TAC `len1 = val(read X13 s0:int64)` THEN
   ARM_STEPS_TAC MLDSA_REJ_UNIFORM_ETA4_EXEC [1] THEN
   SUBGOAL_THEN `read X12 s1:int64 = word len0` ASSUME_TAC THENL
    [REWRITE_TAC[GSYM VAL_EQ] THEN ASM_REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN
     MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC; ALL_TAC] THEN
   SUBGOAL_THEN `read X13 s1:int64 = word len1` ASSUME_TAC THENL
    [REWRITE_TAC[GSYM VAL_EQ] THEN ASM_REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN
     MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC; ALL_TAC] THEN
   ARM_VERBOSE_STEP_TAC MLDSA_REJ_UNIFORM_ETA4_EXEC "s2" THEN
   FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE RAND_CONV [WORD_ADD_SHL1]) THEN
   ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
   SUBGOAL_THEN
    `nonoverlapping (word_add stackpointer (word(2 * (curlen + len0))):int64,
                     16) (word pc:int64, 344)`
   ASSUME_TAC THENL [NONOVERLAPPING_TAC; ALL_TAC] THEN
   ARM_STEPS_TAC MLDSA_REJ_UNIFORM_ETA4_EXEC [3] THEN
   ARM_VERBOSE_STEP_TAC MLDSA_REJ_UNIFORM_ETA4_EXEC "s4" THEN
   FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE RAND_CONV [WORD_ADD_SHL1]) THEN
   ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
   ARM_STEPS_TAC MLDSA_REJ_UNIFORM_ETA4_EXEC (5--6) THEN
   ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
   CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
   SUBGOAL_THEN `8 * (i + 1) <= LENGTH(inlist:byte list)` ASSUME_TAC THENL
    [ASM_REWRITE_TAC[] THEN
     MP_TAC(ASSUME `8 * (i + 1) <= buflen`) THEN ARITH_TAC;
     ALL_TAC] THEN
   MP_TAC(SPECL [`inlist:byte list`; `i:num`] REJ_NIBBLES_ETA4_STEP) THEN
   ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
   ABBREV_TAC `newbatch = REJ_NIBBLES_ETA4(SUB_LIST(8*i, 8) inlist):int16 list` THEN
   REWRITE_TAC[LENGTH_APPEND] THEN ASM_REWRITE_TAC[] THEN
   SUBGOAL_THEN `len0 + len1 = LENGTH(newbatch:int16 list)` ASSUME_TAC THENL
    [ASM_REWRITE_TAC[]; ALL_TAC] THEN
   REPEAT CONJ_TAC THENL
    [AP_TERM_TAC THEN AP_TERM_TAC THEN ASM_ARITH_TAC;
     FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC
       (RAND_CONV o RAND_CONV) [SYM th]) THEN
     REWRITE_TAC[ARITH_RULE `a + b + c = a + (b + c)`] THEN
     CONV_TAC WORD_RULE;
     CHEAT_TAC];  (* CHEAT: memory = num_of_wordlist(APPEND curlist newbatch) *)

   (*** Subgoal 4: Back edge — 2 ARM steps from pc+248 to pc+108 ***)
   X_GEN_TAC `i:num` THEN STRIP_TAC THEN
   CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
   ENSURES_INIT_TAC "s0" THEN
   SUBGOAL_THEN `8 <= val(word_sub (word buflen:int64) (word(8 * i)))`
   ASSUME_TAC THENL
    [SUBGOAL_THEN `8 * (i + 1) <= buflen` ASSUME_TAC THENL
      [MP_TAC(ASSUME `8 divides buflen`) THEN
       REWRITE_TAC[DIVIDES_DIV_MULT] THEN
       UNDISCH_TAC `i < buflen DIV 8` THEN ARITH_TAC; ALL_TAC] THEN
     SUBGOAL_THEN `8 * i < 2 EXP 64` ASSUME_TAC THENL
      [UNDISCH_TAC `buflen < 2 EXP 64` THEN
       UNDISCH_TAC `8 * (i + 1) <= buflen` THEN ARITH_TAC; ALL_TAC] THEN
     VAL_INT64_TAC `8 * i` THEN ASM_REWRITE_TAC[VAL_WORD_SUB_CASES] THEN
     UNDISCH_TAC `8 * (i + 1) <= buflen` THEN ARITH_TAC; ALL_TAC] THEN
   ARM_STEPS_TAC MLDSA_REJ_UNIFORM_ETA4_EXEC (1--2) THEN
   ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[];

   (*** Subgoal 5: Post-loop exit — from pc+248 to pc+256 ***)
   (*** After buflen DIV 8 iterations, remaining = 0, BCS not taken ***)
   CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
   SUBGOAL_THEN `8 * buflen DIV 8 = buflen`
     (fun th -> REWRITE_TAC[th]) THENL
    [MP_TAC(ASSUME `8 divides buflen`) THEN
     REWRITE_TAC[DIVIDES_DIV_MULT] THEN ARITH_TAC; ALL_TAC] THEN
   SUBGOAL_THEN `SUB_LIST(0,buflen) inlist = inlist:byte list`
     (fun th -> REWRITE_TAC[th]) THENL
    [MATCH_MP_TAC SUB_LIST_REFL THEN ASM_REWRITE_TAC[LE_REFL];
     ALL_TAC] THEN
   SUBGOAL_THEN
    `~(8 <= val(word_sub (word buflen:int64) (word buflen)))`
   ASSUME_TAC THENL
    [REWRITE_TAC[WORD_SUB_REFL; VAL_WORD_0] THEN ARITH_TAC;
     ALL_TAC] THEN
   ENSURES_INIT_TAC "s0" THEN
   ARM_STEPS_TAC MLDSA_REJ_UNIFORM_ETA4_EXEC (1--2) THEN
   ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[ALL]]);;
