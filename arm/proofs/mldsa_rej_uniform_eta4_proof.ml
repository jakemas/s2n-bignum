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

let NIBBLES_OF_BYTES_SPLIT4 = prove
 (`!b0 b1 b2 b3 b4 b5 b6 b7:byte.
   NIBBLES_OF_BYTES [b0;b1;b2;b3;b4;b5;b6;b7] =
   APPEND (NIBBLES_OF_BYTES [b0;b1;b2;b3])
          (NIBBLES_OF_BYTES [b4;b5;b6;b7]:int16 list)`,
  REWRITE_TAC[NIBBLES_OF_BYTES; NIBBLE_PAIR; APPEND]);;

let NIBBLES_OF_BYTES_4 = prove
 (`!b0 b1 b2 b3:byte.
   NIBBLES_OF_BYTES [b0;b1;b2;b3] =
   [word(val b0 MOD 16); word(val b0 DIV 16);
    word(val b1 MOD 16); word(val b1 DIV 16);
    word(val b2 MOD 16); word(val b2 DIV 16);
    word(val b3 MOD 16); word(val b3 DIV 16):int16]`,
  REWRITE_TAC[NIBBLES_OF_BYTES; NIBBLE_PAIR; APPEND]);;

let VAL_WORD_NIBBLE_LT = prove
 (`!b:byte.
   val(word(val b MOD 16):int16) = val b MOD 16 /\
   val(word(val b DIV 16):int16) = val b DIV 16`,
  GEN_TAC THEN REWRITE_TAC[VAL_WORD; DIMINDEX_16] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  CONJ_TAC THEN MATCH_MP_TAC MOD_LT THEN
  MP_TAC(ISPEC `b:byte` VAL_BOUND) THEN
  REWRITE_TAC[DIMINDEX_8] THEN ARITH_TAC);;

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

let REJ_NIBBLES_COUNT_4 = prove
 (`!b0 b1 b2 b3:byte.
   LENGTH(FILTER (\x:int16. val x < 9) (NIBBLES_OF_BYTES [b0;b1;b2;b3])) =
   bitval(val b0 MOD 16 < 9) + bitval(val b0 DIV 16 < 9) +
   bitval(val b1 MOD 16 < 9) + bitval(val b1 DIV 16 < 9) +
   bitval(val b2 MOD 16 < 9) + bitval(val b2 DIV 16 < 9) +
   bitval(val b3 MOD 16 < 9) + bitval(val b3 DIV 16 < 9)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[NIBBLES_OF_BYTES_4] THEN
  REWRITE_TAC[ISPECL [`word(val(b0:byte) MOD 16):int16`;
    `word(val(b0:byte) DIV 16):int16`;
    `word(val(b1:byte) MOD 16):int16`;
    `word(val(b1:byte) DIV 16):int16`;
    `word(val(b2:byte) MOD 16):int16`;
    `word(val(b2:byte) DIV 16):int16`;
    `word(val(b3:byte) MOD 16):int16`;
    `word(val(b3:byte) DIV 16):int16`] FILTER_LENGTH_BITVAL] THEN
  REWRITE_TAC[VAL_WORD_NIBBLE_LT]);;

let REJ_NIBBLES_COUNT_8 = prove
 (`!b0 b1 b2 b3 b4 b5 b6 b7:byte.
   LENGTH(REJ_NIBBLES_ETA4 [b0;b1;b2;b3;b4;b5;b6;b7]) =
   (bitval(val b0 MOD 16 < 9) + bitval(val b0 DIV 16 < 9) +
    bitval(val b1 MOD 16 < 9) + bitval(val b1 DIV 16 < 9) +
    bitval(val b2 MOD 16 < 9) + bitval(val b2 DIV 16 < 9) +
    bitval(val b3 MOD 16 < 9) + bitval(val b3 DIV 16 < 9)) +
   bitval(val b4 MOD 16 < 9) + bitval(val b4 DIV 16 < 9) +
   bitval(val b5 MOD 16 < 9) + bitval(val b5 DIV 16 < 9) +
   bitval(val b6 MOD 16 < 9) + bitval(val b6 DIV 16 < 9) +
   bitval(val b7 MOD 16 < 9) + bitval(val b7 DIV 16 < 9)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[REJ_NIBBLES_ETA4; NIBBLES_OF_BYTES_SPLIT4] THEN
  REWRITE_TAC[FILTER_APPEND; LENGTH_APPEND] THEN
  REWRITE_TAC[REJ_NIBBLES_COUNT_4]);;

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

let NIBLEN_BOUND_FROM_WOP = prove
 (`!inlist:byte list. !N.
   0 < N /\
   (!m. m < N ==> 8 * (m + 1) <= LENGTH inlist /\
        LENGTH(REJ_NIBBLES_ETA4(SUB_LIST(0,8*m) inlist)) < 256)
   ==> LENGTH(REJ_NIBBLES_ETA4(SUB_LIST(0,8*N) inlist):int16 list) < 272`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `N - 1`) THEN
  ASM_REWRITE_TAC[ARITH_RULE `N - 1 < N <=> 0 < N`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `8 * N = 0 + 8 * (N - 1) + 8` SUBST1_TAC THENL
   [UNDISCH_TAC `0 < N` THEN ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[SUB_LIST_SPLIT; SUB_LIST_CLAUSES; APPEND; ADD_CLAUSES] THEN
  REWRITE_TAC[REJ_NIBBLES_ETA4_APPEND; LENGTH_APPEND] THEN
  MP_TAC(ISPEC `SUB_LIST(8*(N-1),8) inlist:byte list`
    LENGTH_REJ_NIBBLES_ETA4) THEN
  REWRITE_TAC[LENGTH_SUB_LIST] THEN
  UNDISCH_TAC
   `LENGTH(REJ_NIBBLES_ETA4(SUB_LIST(0,8*(N-1)) inlist):int16 list) < 256` THEN
  ARITH_TAC);;

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

(* Byte-level nibble extraction lemmas (for counting bridge) *)
let BYTE_AND_15_MOD = BITBLAST_RULE
  `val(word_and (b:byte) (word 15):byte) = val b MOD 16`;;

let BYTE_USHR4_DIV = WORD_BLAST
  `val(word_ushr (b:byte) 4:byte) = val b DIV 16`;;

let VAL_WORD_ZX_BYTE16 = WORD_BLAST
  `val(word_zx (b:byte):int16) = val b`;;

let BYTE_NIBBLE_COUNT_EQ = prove(
  `!b:byte.
   bitval(val(word_zx(word_and b (word 15):byte):int16) < 9) +
   bitval(val(word_zx(word_ushr b 4:byte):int16) < 9) =
   bitval(val b MOD 16 < 9) + bitval(val b DIV 16 < 9)`,
  GEN_TAC THEN
  REWRITE_TAC[VAL_WORD_ZX_BYTE16; BYTE_AND_15_MOD; BYTE_USHR4_DIV]);;

(* Byte-indexed counting identity: for any d:int64, sum over j=0..7 of             *)
(* bitvals for low/high nibbles of byte j equals                                   *)
(* LENGTH(REJ_NIBBLES_ETA4 [byte0 d; byte1 d; ...; byte7 d]).                       *)
(* This is NIBBLE_COUNTING_D — a lemma useful for closing CHEAT #2 when we have    *)
(* expressed nibbles0 / nibbles1b as USHLL(ZIP1/ZIP2(AND/USHR of d)).               *)
let NIBBLE_COUNTING_D = prove(
 `!d:int64.
    let b = \j. word_subword d (8 * j, 8):byte in
    bitval(val(word_zx(word_and (b 0) (word 15):byte):int16) < 9) +
    bitval(val(word_zx(word_ushr (b 0) 4:byte):int16) < 9) +
    bitval(val(word_zx(word_and (b 1) (word 15):byte):int16) < 9) +
    bitval(val(word_zx(word_ushr (b 1) 4:byte):int16) < 9) +
    bitval(val(word_zx(word_and (b 2) (word 15):byte):int16) < 9) +
    bitval(val(word_zx(word_ushr (b 2) 4:byte):int16) < 9) +
    bitval(val(word_zx(word_and (b 3) (word 15):byte):int16) < 9) +
    bitval(val(word_zx(word_ushr (b 3) 4:byte):int16) < 9) +
    bitval(val(word_zx(word_and (b 4) (word 15):byte):int16) < 9) +
    bitval(val(word_zx(word_ushr (b 4) 4:byte):int16) < 9) +
    bitval(val(word_zx(word_and (b 5) (word 15):byte):int16) < 9) +
    bitval(val(word_zx(word_ushr (b 5) 4:byte):int16) < 9) +
    bitval(val(word_zx(word_and (b 6) (word 15):byte):int16) < 9) +
    bitval(val(word_zx(word_ushr (b 6) 4:byte):int16) < 9) +
    bitval(val(word_zx(word_and (b 7) (word 15):byte):int16) < 9) +
    bitval(val(word_zx(word_ushr (b 7) 4:byte):int16) < 9) =
    LENGTH(REJ_NIBBLES_ETA4 [b 0; b 1; b 2; b 3; b 4; b 5; b 6; b 7])`,
  GEN_TAC THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[REJ_NIBBLES_COUNT_8] THEN
  REWRITE_TAC[VAL_WORD_ZX_BYTE16; BYTE_AND_15_MOD; BYTE_USHR4_DIV] THEN
  ARITH_TAC);;

(* Abstract counting bridge: given that nibbles0 and nibbles1b have halfwords       *)
(* equal to byte-nibble expressions, the 16-halfword bitval sum equals              *)
(* LENGTH(REJ_NIBBLES_ETA4 [b0;b1;...;b7]).                                         *)
let COUNT_BRIDGE_ABSTRACT = prove(
  `!x0:int128. !x1:int128. !b0 b1 b2 b3 b4 b5 b6 b7:byte.
      word_subword x0 (0,16):int16 = word_zx(word_and b0 (word 15):byte):int16 /\
      word_subword x0 (16,16):int16 = word_zx(word_ushr b0 4:byte):int16 /\
      word_subword x0 (32,16):int16 = word_zx(word_and b1 (word 15):byte):int16 /\
      word_subword x0 (48,16):int16 = word_zx(word_ushr b1 4:byte):int16 /\
      word_subword x0 (64,16):int16 = word_zx(word_and b2 (word 15):byte):int16 /\
      word_subword x0 (80,16):int16 = word_zx(word_ushr b2 4:byte):int16 /\
      word_subword x0 (96,16):int16 = word_zx(word_and b3 (word 15):byte):int16 /\
      word_subword x0 (112,16):int16 = word_zx(word_ushr b3 4:byte):int16 /\
      word_subword x1 (0,16):int16 = word_zx(word_and b4 (word 15):byte):int16 /\
      word_subword x1 (16,16):int16 = word_zx(word_ushr b4 4:byte):int16 /\
      word_subword x1 (32,16):int16 = word_zx(word_and b5 (word 15):byte):int16 /\
      word_subword x1 (48,16):int16 = word_zx(word_ushr b5 4:byte):int16 /\
      word_subword x1 (64,16):int16 = word_zx(word_and b6 (word 15):byte):int16 /\
      word_subword x1 (80,16):int16 = word_zx(word_ushr b6 4:byte):int16 /\
      word_subword x1 (96,16):int16 = word_zx(word_and b7 (word 15):byte):int16 /\
      word_subword x1 (112,16):int16 = word_zx(word_ushr b7 4:byte):int16
      ==>
      bitval(val(word_subword x0 (0,16):int16) < 9) +
      bitval(val(word_subword x0 (16,16):int16) < 9) +
      bitval(val(word_subword x0 (32,16):int16) < 9) +
      bitval(val(word_subword x0 (48,16):int16) < 9) +
      bitval(val(word_subword x0 (64,16):int16) < 9) +
      bitval(val(word_subword x0 (80,16):int16) < 9) +
      bitval(val(word_subword x0 (96,16):int16) < 9) +
      bitval(val(word_subword x0 (112,16):int16) < 9) +
      bitval(val(word_subword x1 (0,16):int16) < 9) +
      bitval(val(word_subword x1 (16,16):int16) < 9) +
      bitval(val(word_subword x1 (32,16):int16) < 9) +
      bitval(val(word_subword x1 (48,16):int16) < 9) +
      bitval(val(word_subword x1 (64,16):int16) < 9) +
      bitval(val(word_subword x1 (80,16):int16) < 9) +
      bitval(val(word_subword x1 (96,16):int16) < 9) +
      bitval(val(word_subword x1 (112,16):int16) < 9) =
      LENGTH(REJ_NIBBLES_ETA4 [b0;b1;b2;b3;b4;b5;b6;b7])`,
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN SUBST1_TAC) THEN
  REWRITE_TAC[REJ_NIBBLES_COUNT_8] THEN
  REWRITE_TAC[VAL_WORD_ZX_BYTE16; BYTE_AND_15_MOD; BYTE_USHR4_DIV] THEN
  ARITH_TAC);;

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
Printf.printf "DEBUG: entering proof tactic\n%!";;

let DBG msg = fun g ->
  let (hyps, goal) = g in
  Printf.printf "DEBUG: %s | %d hyps | goal head: %s\n%!" msg
    (List.length hyps)
    (let s = string_of_term goal in
     if String.length s > 100 then String.sub s 0 100 else s);
  ALL_TAC g;;

(* Takes ~60 seconds total *)
(* Key technique: ENSURES_SEQUENCE_TAC within loop body at pc+0xD8 *)
(* to capture X12/X13 bounds before ST1 stores.                   *)
(* ARM_VERBOSE_STEP_TAC for FMOV exposes symbolic X12/X13.        *)

e (DBG "01 START" THEN
 REWRITE_TAC[LENGTH_MLDSA_REJ_UNIFORM_ETA4_MC;
    fst MLDSA_REJ_UNIFORM_ETA4_EXEC;
    MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI;
    C_ARGUMENTS; ALL; C_RETURN] THEN
 MAP_EVERY X_GEN_TAC [`res:int64`; `buf:int64`] THEN
 W64_GEN_TAC `buflen:num` THEN
 MAP_EVERY X_GEN_TAC
  [`table:int64`; `inlist:byte list`; `pc:num`; `stackpointer:int64`] THEN
 DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
 DBG "02 after DISCH" THEN

 (* === Split: computation (pc+4 to pc+256) and writeback (to pc+336) === *)
 (* Intermediate postcondition at pc+256 (CMP X9,X4 instruction) tracks   *)
 (* REJ_NIBBLES_ETA4(inlist) directly -- no existential, no niblen bound. *)
 (* Loop uses buflen DIV 8 iterations: exhausts entire buffer, BCS        *)
 (* deterministically not taken after last iteration.                      *)
 (* Intermediate state at pc+256: uses existential n for processed prefix *)
 ENSURES_SEQUENCE_TAC `pc + 256`
  `\s. aligned_bytes_loaded s (word pc) mldsa_rej_uniform_eta4_mc /\
       read PC s = word(pc + 256) /\
       read X0 s = res /\ read X4 s = word 256 /\
       read X8 s = stackpointer /\
       read Q7 s = word 20769504351625144638033088116686852 /\
       ALL (nonoverlapping (res,1024)) [(word pc,344); (stackpointer,576)] /\
       ?n. let niblist = REJ_NIBBLES_ETA4(SUB_LIST(0,8*n) inlist) in
           let niblen = LENGTH niblist in
           niblen < 272 /\
           (buflen < 8 * (n + 1) \/ 256 <= niblen) /\
           read X9 s = word niblen /\
           read (memory :> bytes (stackpointer,2 * niblen)) s =
           num_of_wordlist niblist` THEN
 CONJ_TAC THENL
  [DBG "03 computation branch";

   (*** Writeback phase: pc+256 to pc+336 ***)
   DBG "04 writeback branch start" THEN
   (*** Uses partial niblist = REJ_NIBBLES_ETA4(SUB_LIST(0,8*n) inlist) ***)
   ENSURES_INIT_TAC "s0" THEN
   DBG "04a after ENSURES_INIT" THEN
   FIRST_X_ASSUM(X_CHOOSE_THEN `nn:num` MP_TAC) THEN
   DBG "04b after X_CHOOSE" THEN
   CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
   DBG "04c after let_CONV" THEN
   ABBREV_TAC `niblist = REJ_NIBBLES_ETA4
     (SUB_LIST(0,8*nn) inlist):int16 list` THEN
   DBG "04d after ABBREV niblist" THEN
   ABBREV_TAC `niblen = LENGTH(niblist:int16 list)` THEN
   DBG "04e after ABBREV niblen" THEN
   CHEAT_TAC] THEN  (* CHEAT: writeback memory content (was broken in original) *)

 (* === WOP: find smallest N where loop exits === *)
 (* N is the first iteration where either buffer exhausted or 256 samples *)
 SUBGOAL_THEN
  `?N. buflen < 8 * (N + 1) \/
       256 <= LENGTH(REJ_NIBBLES_ETA4(SUB_LIST(0,8*N) inlist):int16 list)`
 MP_TAC THENL
  [EXISTS_TAC `buflen:num` THEN DISJ1_TAC THEN ARITH_TAC;
   GEN_REWRITE_TAC LAND_CONV [num_WOP]] THEN
 DISCH_THEN(X_CHOOSE_THEN `N:num`
   (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
 REWRITE_TAC[DE_MORGAN_THM; NOT_LT; NOT_LE] THEN STRIP_TAC THEN

 (* For all i < N: 8*(i+1) <= buflen AND LENGTH(...) < 256 *)

 SUBGOAL_THEN `0 < N` ASSUME_TAC THENL
  [(* ASM_ARITH_TAC times out on many irrelevant hyps; use MP_TAC + ARITH *)
   MP_TAC(ASSUME `buflen < 8 * (N + 1) \/
     256 <= LENGTH(REJ_NIBBLES_ETA4(SUB_LIST(0,8*N) inlist):int16 list)`) THEN
   UNDISCH_TAC `8 <= buflen` THEN
   STRUCT_CASES_TAC (ARITH_RULE `N = 0 \/ 0 < N`) THEN
   ASM_REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES; SUB_LIST_CLAUSES;
                   REJ_NIBBLES_ETA4_EMPTY; LENGTH] THEN
   ARITH_TAC;
   ALL_TAC] THEN

 DBG "05 before ENSURES_WHILE_UP_TAC" THEN
 ENSURES_WHILE_UP_TAC `N:num` `pc + 108` `pc + 248`
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
  [(*** Subgoal 1: 0 < N ***)
   DBG "06 subgoal1 0<N" THEN ASM_ARITH_TAC;

   (*** Subgoal 2: Pre-loop init (75 ARM steps) ***)
   DBG "07 subgoal2 preamble" THEN
   GHOST_INTRO_TAC `q31_init:int128` `read Q31` THEN
   ENSURES_INIT_TAC "s0" THEN
   ARM_STEPS_TAC MLDSA_REJ_UNIFORM_ETA4_EXEC (1--75) THEN
   ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
   CONJ_TAC THENL [REWRITE_TAC[WORD_INSERT_Q31]; ALL_TAC] THEN
   REWRITE_TAC[MULT_CLAUSES; SUB_LIST_CLAUSES; REJ_NIBBLES_ETA4_EMPTY] THEN
   CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REWRITE_TAC[LENGTH] THEN
   REWRITE_TAC[MULT_CLAUSES; WORD_ADD_0; WORD_SUB_0] THEN
   REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_TRIVIAL; num_of_wordlist];

   (*** Subgoal 3: Loop body — split at pc+0xe0, with Q16/Q17 content ***)
   DBG "08 subgoal3 loop body" THEN
   X_GEN_TAC `i:num` THEN STRIP_TAC THEN
   DBG "08a after X_GEN+STRIP" THEN
   ABBREV_TAC `curlist = REJ_NIBBLES_ETA4(SUB_LIST(0,8 * i) inlist)` THEN
   ABBREV_TAC `curlen = LENGTH(curlist:int16 list)` THEN
   DBG "08b after ABBREVs" THEN
   SUBGOAL_THEN `curlen < 256` ASSUME_TAC THENL
    [EXPAND_TAC "curlen" THEN EXPAND_TAC "curlist" THEN
     FIRST_X_ASSUM(MP_TAC o SPEC `i:num`) THEN
     UNDISCH_TAC `i < N:num` THEN ARITH_TAC; ALL_TAC] THEN
   DBG "08c after curlen<256" THEN
   SUBGOAL_THEN `8 * (i + 1) <= buflen` ASSUME_TAC THENL
    [FIRST_X_ASSUM(MP_TAC o SPEC `i:num`) THEN
     UNDISCH_TAC `i < N:num` THEN ARITH_TAC; ALL_TAC] THEN
   DBG "08d after 8*(i+1)<=buflen" THEN
   CONV_TAC(RATOR_CONV(LAND_CONV(TOP_DEPTH_CONV let_CONV))) THEN
   ASM_REWRITE_TAC[] THEN
   DBG "08e after let_CONV+ASM_REWRITE" THEN
   (* removed spurious ENSURES_INIT_TAC that was breaking ENSURES_SEQUENCE_TAC *)
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
    [(* First half: SIMD compute chain — 29 steps *)
     DBG "09 first half start" THEN
     GHOST_INTRO_TAC `nibbles1:int128` `read Q17` THEN
     ENSURES_INIT_TAC "s0" THEN
     ARM_STEPS_TAC MLDSA_REJ_UNIFORM_ETA4_EXEC (1--2) THEN
     SUBGOAL_THEN `~(256 <= val(word curlen:int64))` ASSUME_TAC THENL
      [REWRITE_TAC[NOT_LE; VAL_WORD; DIMINDEX_64] THEN
       CONV_TAC NUM_REDUCE_CONV THEN
       SUBGOAL_THEN `curlen MOD 18446744073709551616 = curlen`
        SUBST1_TAC THENL
        [MATCH_MP_TAC MOD_LT THEN UNDISCH_TAC `curlen < 256` THEN
         ARITH_TAC; UNDISCH_TAC `curlen < 256` THEN ARITH_TAC];
       ALL_TAC] THEN
     RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `~(256 <= val(word curlen:int64))`]) THEN
     (* Step 3 = LDR D0 loading 8 bytes from X1 = buf + 8*i *)
     ARM_STEPS_TAC MLDSA_REJ_UNIFORM_ETA4_EXEC [3] THEN
     (* Preserve d = loaded memory for later use in the counting bridge *)
     ABBREV_TAC `loaded_d:int64 = read (memory :> bytes64 (word_add buf (word (8 * i)))) s3` THEN
     (* Use verbose stepping for 4--11 so Q16 s11 / Q17 s11 remain as named hyps *)
     ARM_VSTEPS_TAC MLDSA_REJ_UNIFORM_ETA4_EXEC (4--11) THEN
     REABBREV_TAC `nibbles0:int128 = read Q16 s11` THEN
     REABBREV_TAC `nibbles1b:int128 = read Q17 s11` THEN
     ARM_STEPS_TAC MLDSA_REJ_UNIFORM_ETA4_EXEC (12--19) THEN
     RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV)) THEN
     RULE_ASSUM_TAC(CONV_RULE WORD_REDUCE_CONV) THEN
     RULE_ASSUM_TAC(REWRITE_RULE
      [word_ugt; relational2; GT; WORD_AND_MASK]) THEN
     RULE_ASSUM_TAC(ONCE_REWRITE_RULE[COND_RAND]) THEN
     RULE_ASSUM_TAC(CONV_RULE WORD_REDUCE_CONV) THEN
     ARM_STEPS_TAC MLDSA_REJ_UNIFORM_ETA4_EXEC (20--25) THEN
     RULE_ASSUM_TAC(REWRITE_RULE[WORD_SUBWORD_AND]) THEN
     RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV)) THEN
     RULE_ASSUM_TAC(CONV_RULE WORD_REDUCE_CONV) THEN
     RULE_ASSUM_TAC(REWRITE_RULE
      [word_ugt; relational2; GT; WORD_AND_MASK]) THEN
     RULE_ASSUM_TAC(ONCE_REWRITE_RULE[COND_RAND]) THEN
     RULE_ASSUM_TAC(CONV_RULE WORD_REDUCE_CONV) THEN
     ARM_STEPS_TAC MLDSA_REJ_UNIFORM_ETA4_EXEC (26--29) THEN
     DBG "10 after steps 1-29" THEN
     ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
     ASM_REWRITE_TAC[WORD_SUBWORD_AND] THEN
     CONV_TAC(DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
     CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV) THEN
     REWRITE_TAC[WORD_AND_0; WORD_POPCOUNT_0; ADD_CLAUSES] THEN
     REWRITE_TAC[POPCOUNT_AND_POWERS] THEN
     DBG "11 before REPEAT CONJ_TAC" THEN
     REPEAT CONJ_TAC THEN
     DBG "12 after REPEAT CONJ_TAC" THEN
     TRY(CONV_TAC WORD_RULE) THEN
     TRY(NONOVERLAPPING_TAC) THEN
     TRY(REWRITE_TAC[UADDLV_BOUND_LEMMA] THEN NO_TAC) THEN
     DBG "13 after BOUND TRY" THEN
     TRY(DBG "14a TRY counting bridge entry" THEN
         REWRITE_TAC[UADDLV_COUNT_LEMMA] THEN
         REWRITE_TAC(List.map (fun k -> BITBLAST_RULE
           (vsubst [mk_small_numeral k, `k:num`]
           `bit k (word_subword (word_neg (word (bitval b):16 word))
                   (0,8):8 word) <=> b`)) (0--7)) THEN
         DBG "14b after bit-k rewrites" THEN
         ASM_REWRITE_TAC[] THEN
         DBG "14c after ASM_REWRITE" THEN
         (* Counting bridge: apply COUNT_BRIDGE_ABSTRACT with 16 halfword
            identities derived from nibbles0 / nibbles1b = f(loaded_d), then
            collapse sum via NIBBLE_COUNTING_D. *)
         (let prove_hw name pos byte_pos op =
            let rhs_inner = if op = "and"
              then Printf.sprintf
                "(word_and (word_subword (loaded_d:int64) (%d,8):byte) (word 15):byte)"
                byte_pos
              else Printf.sprintf
                "(word_ushr (word_subword (loaded_d:int64) (%d,8):byte) 4:byte)"
                byte_pos in
            let goal_str = Printf.sprintf
              "(word_subword (%s:int128) (%d,16)):int16 = word_zx %s :int16"
              name pos rhs_inner in
            SUBGOAL_THEN (parse_term goal_str) ASSUME_TAC THENL
             [FIRST_X_ASSUM(MP_TAC o SYM o check
                (fun th -> let c = concl th in is_eq c &&
                  (try fst(dest_var(rhs c)) = name with _ -> false))) THEN
              DISCH_THEN(fun th -> SUBST1_TAC th THEN ASSUME_TAC(SYM th)) THEN
              CONV_TAC WORD_BLAST;
              ALL_TAC] in
          prove_hw "nibbles0" 0 0 "and" THEN
          prove_hw "nibbles0" 16 0 "ushr" THEN
          prove_hw "nibbles0" 32 8 "and" THEN
          prove_hw "nibbles0" 48 8 "ushr" THEN
          prove_hw "nibbles0" 64 16 "and" THEN
          prove_hw "nibbles0" 80 16 "ushr" THEN
          prove_hw "nibbles0" 96 24 "and" THEN
          prove_hw "nibbles0" 112 24 "ushr" THEN
          prove_hw "nibbles1b" 0 32 "and" THEN
          prove_hw "nibbles1b" 16 32 "ushr" THEN
          prove_hw "nibbles1b" 32 40 "and" THEN
          prove_hw "nibbles1b" 48 40 "ushr" THEN
          prove_hw "nibbles1b" 64 48 "and" THEN
          prove_hw "nibbles1b" 80 48 "ushr" THEN
          prove_hw "nibbles1b" 96 56 "and" THEN
          prove_hw "nibbles1b" 112 56 "ushr") THEN
         DBG "14d after prove_hw 16x" THEN
         MP_TAC(SPECL
           [`nibbles0:int128`; `nibbles1b:int128`;
            `word_subword (loaded_d:int64) (0,8):byte`;
            `word_subword (loaded_d:int64) (8,8):byte`;
            `word_subword (loaded_d:int64) (16,8):byte`;
            `word_subword (loaded_d:int64) (24,8):byte`;
            `word_subword (loaded_d:int64) (32,8):byte`;
            `word_subword (loaded_d:int64) (40,8):byte`;
            `word_subword (loaded_d:int64) (48,8):byte`;
            `word_subword (loaded_d:int64) (56,8):byte`] COUNT_BRIDGE_ABSTRACT) THEN
         DBG "14e after MP_TAC bridge" THEN
         ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
         DBG "14f after ANTS" THEN
         DISCH_THEN SUBST1_TAC THEN
         DBG "14g after DISCH_THEN SUBST1" THEN
         ASM_REWRITE_TAC[] THEN
         DBG "14h after ASM_REWRITE" THEN
         (* TRANS via [bytes of loaded_d] list: first half by
            NIBBLE_COUNTING_D, second half by SUB_LIST = [bytes] *)
         TRANS_TAC EQ_TRANS
           `LENGTH(REJ_NIBBLES_ETA4
              [word_subword (loaded_d:int64) (0,8):byte;
               word_subword (loaded_d:int64) (8,8):byte;
               word_subword (loaded_d:int64) (16,8):byte;
               word_subword (loaded_d:int64) (24,8):byte;
               word_subword (loaded_d:int64) (32,8):byte;
               word_subword (loaded_d:int64) (40,8):byte;
               word_subword (loaded_d:int64) (48,8):byte;
               word_subword (loaded_d:int64) (56,8):byte])` THEN
         DBG "14i after TRANS_TAC" THEN
         CONJ_TAC THENL
          [DBG "14j first CONJ branch" THEN
           MP_TAC(SPEC `loaded_d:int64` NIBBLE_COUNTING_D) THEN
           REWRITE_TAC[LET_DEF; LET_END_DEF] THEN BETA_TAC THEN
           CONV_TAC NUM_REDUCE_CONV THEN
           DISCH_THEN(fun th -> MP_TAC th THEN ARITH_TAC);
           DBG "14k second CONJ branch" THEN
           AP_TERM_TAC THEN AP_TERM_TAC THEN
           DBG "14l after AP_TERM_TAC x2" THEN
           (* SUB_LIST(8*i, 8) inlist = [bytes of loaded_d] follows from
              memory read: loaded_d = read bytes64(buf+8*i) s3 and
              read bytes(buf,buflen) = num_of_wordlist inlist. *)
           DBG "14m before CHEAT_TAC" THEN
           CHEAT_TAC]) THEN
     DBG "14n after second CONJ closes" THEN
     ASM_ARITH_TAC;
     ALL_TAC] THEN
   (* Second half: ST1 stores + accumulation — 6 steps *)
   DBG "15 second half start" THEN
   ENSURES_INIT_TAC "s0" THEN
   DBG "15a after ENSURES_INIT" THEN
   ABBREV_TAC `len0 = val(read X12 s0:int64)` THEN
   ABBREV_TAC `len1 = val(read X13 s0:int64)` THEN
   DBG "15b after ABBREV len0/len1" THEN
   ARM_STEPS_TAC MLDSA_REJ_UNIFORM_ETA4_EXEC [1] THEN
   DBG "15c after ARM step 1" THEN
   SUBGOAL_THEN `read X12 s1:int64 = word len0` ASSUME_TAC THENL
    [DBG "15d inside X12 subgoal" THEN
     REWRITE_TAC[GSYM VAL_EQ] THEN ASM_REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN
     DBG "15e after REWRITE" THEN
     CONV_TAC SYM_CONV THEN
     MATCH_MP_TAC MOD_LT THEN
     DBG "15f after MATCH_MP_TAC MOD_LT" THEN
     ASM_ARITH_TAC; ALL_TAC] THEN
   DBG "15g after X12 subgoal" THEN
   SUBGOAL_THEN `read X13 s1:int64 = word len1` ASSUME_TAC THENL
    [REWRITE_TAC[GSYM VAL_EQ] THEN ASM_REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN
     CONV_TAC SYM_CONV THEN
     MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC; ALL_TAC] THEN
   DBG "15h after X13 subgoal" THEN
   ARM_VERBOSE_STEP_TAC MLDSA_REJ_UNIFORM_ETA4_EXEC "s2" THEN
   DBG "15i after VSTEP s2" THEN
   FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE RAND_CONV [WORD_ADD_SHL1]) THEN
   ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
   DBG "15j after WORD_ADD_SHL1 rewrite" THEN
   SUBGOAL_THEN
    `nonoverlapping (word_add stackpointer (word(2 * (curlen + len0))):int64,
                     16) (word pc:int64, 344)`
   ASSUME_TAC THENL [NONOVERLAPPING_TAC; ALL_TAC] THEN
   DBG "15k after nonoverlapping subgoal" THEN
   ARM_STEPS_TAC MLDSA_REJ_UNIFORM_ETA4_EXEC [3] THEN
   DBG "15l after ARM step 3" THEN
   ARM_VERBOSE_STEP_TAC MLDSA_REJ_UNIFORM_ETA4_EXEC "s4" THEN
   DBG "15m after VSTEP s4" THEN
   FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE RAND_CONV [WORD_ADD_SHL1]) THEN
   ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
   DBG "15n after WORD_ADD_SHL1 rewrite 2" THEN
   ARM_STEPS_TAC MLDSA_REJ_UNIFORM_ETA4_EXEC (5--6) THEN
   DBG "15o after ARM steps 5-6" THEN
   ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
   DBG "15p after ENSURES_FINAL" THEN
   CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
   DBG "15q after let_CONV" THEN
   SUBGOAL_THEN `8 * (i + 1) <= LENGTH(inlist:byte list)` ASSUME_TAC THENL
    [ASM_REWRITE_TAC[] THEN
     MP_TAC(ASSUME `8 * (i + 1) <= buflen`) THEN ARITH_TAC;
     ALL_TAC] THEN
   DBG "15r after 8*(i+1)<=LENGTH" THEN
   MP_TAC(SPECL [`inlist:byte list`; `i:num`] REJ_NIBBLES_ETA4_STEP) THEN
   DBG "15s after MP_TAC REJ_NIBBLES_ETA4_STEP" THEN
   ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
   DBG "15t after STEP DISCH" THEN
   ABBREV_TAC `newbatch = REJ_NIBBLES_ETA4(SUB_LIST(8*i, 8) inlist):int16 list` THEN
   DBG "15u after ABBREV newbatch" THEN
   REWRITE_TAC[LENGTH_APPEND] THEN ASM_REWRITE_TAC[] THEN
   DBG "15v after LENGTH_APPEND" THEN
   SUBGOAL_THEN `len0 + len1 = LENGTH(newbatch:int16 list)` ASSUME_TAC THENL
    [ASM_REWRITE_TAC[]; ALL_TAC] THEN
   DBG "15w after len0+len1=LENGTH" THEN
   REPEAT CONJ_TAC THENL
    [DBG "15x final CONJ1" THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
     (* Goal is 2 * ((curlen + val(word len0)) + val(word len1)) = 2 * (curlen + LENGTH newbatch).
        Need val(word len0) = len0 (since len0 < 2^64) and val(word len1) = len1. *)
     ONCE_REWRITE_TAC[GSYM(ASSUME `read X12 s1:int64 = word len0`)] THEN
     ONCE_REWRITE_TAC[GSYM(ASSUME `read X13 s1:int64 = word len1`)] THEN
     DBG "15x' after rewriting word back to read" THEN
     ASM_REWRITE_TAC[] THEN ARITH_TAC;
     DBG "15y final CONJ2" THEN
     FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC
       (RAND_CONV o RAND_CONV) [SYM th]) THEN
     REWRITE_TAC[ARITH_RULE `a + b + c = a + (b + c)`] THEN
     CONV_TAC WORD_RULE;
     DBG "15z final CONJ3 (CHEAT)" THEN CHEAT_TAC];

   (*** Subgoal 4: Back edge — 2 ARM steps from pc+248 to pc+108 ***)
   X_GEN_TAC `i:num` THEN STRIP_TAC THEN
   CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
   ENSURES_INIT_TAC "s0" THEN
   SUBGOAL_THEN `8 <= val(word_sub (word buflen:int64) (word(8 * i)))`
   ASSUME_TAC THENL
    [SUBGOAL_THEN `8 * (i + 1) <= buflen` ASSUME_TAC THENL
      [FIRST_X_ASSUM(MP_TAC o SPEC `i:num`) THEN
       UNDISCH_TAC `i < N:num` THEN ARITH_TAC; ALL_TAC] THEN
     SUBGOAL_THEN `8 * i < 2 EXP 64` ASSUME_TAC THENL
      [UNDISCH_TAC `buflen < 2 EXP 64` THEN
       UNDISCH_TAC `8 * (i + 1) <= buflen` THEN ARITH_TAC; ALL_TAC] THEN
     VAL_INT64_TAC `8 * i` THEN ASM_REWRITE_TAC[VAL_WORD_SUB_CASES] THEN
     UNDISCH_TAC `8 * (i + 1) <= buflen` THEN ARITH_TAC; ALL_TAC] THEN
   ARM_STEPS_TAC MLDSA_REJ_UNIFORM_ETA4_EXEC (1--2) THEN
   ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[];

   (*** Subgoal 5: Post-loop exit — from pc+248 to pc+256 ***)
   (*** WOP: at i=N, either buffer exhausted or 256 <= niblen ***)
   CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
   ABBREV_TAC `niblen = LENGTH(REJ_NIBBLES_ETA4(SUB_LIST(0,8*N) inlist):int16 list)` THEN
   SUBGOAL_THEN `niblen < 272` ASSUME_TAC THENL
    [EXPAND_TAC "niblen" THEN
     MATCH_MP_TAC NIBLEN_BOUND_FROM_WOP THEN
     ASM_REWRITE_TAC[] THEN
     X_GEN_TAC `mm:num` THEN DISCH_TAC THEN
     FIRST_X_ASSUM(MP_TAC o SPEC `mm:num`) THEN
     ASM_REWRITE_TAC[];
     ALL_TAC] THEN
   VAL_INT64_TAC `niblen:num` THEN
   ASM_CASES_TAC `256 <= niblen` THENL
    [(* Case: 256 <= niblen — enough samples *)
     ASM_CASES_TAC `8 <= val(word_sub (word buflen:int64) (word(8 * N)))` THENL
      [(* Subcase: X2 >= 8 — back edge branches to pc+108, then CMP X9>=X4 *)
       (* branches forward to pc+256. Total 4 ARM steps. *)
       (* Split with ENSURES_SEQUENCE_TAC at pc+108 to avoid ARM_STEPS_TAC *)
       (* stack overflow with deeply nested niblen term. *)
       ENSURES_SEQUENCE_TAC `pc + 108`
        `\s. aligned_bytes_loaded s (word pc) mldsa_rej_uniform_eta4_mc /\
             read PC s = word(pc + 108) /\
             read X0 s = res /\ read X4 s = word 256 /\
             read X8 s = stackpointer /\
             read Q7 s = word 20769504351625144638033088116686852 /\
             read X9 s = word niblen /\
             read (memory :> bytes (stackpointer,2 * niblen)) s =
             num_of_wordlist (REJ_NIBBLES_ETA4(SUB_LIST(0,8*N) inlist):int16 list) /\
             ALL (nonoverlapping (res,1024)) [(word pc,344); (stackpointer,576)]` THEN
       CONJ_TAC THENL
        [(* pc+248 -> pc+108: CMP X2,8; BCS back *)
         ENSURES_INIT_TAC "s0" THEN
         ARM_STEPS_TAC MLDSA_REJ_UNIFORM_ETA4_EXEC (1--2) THEN
         ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
         REWRITE_TAC[ALL] THEN ASM_REWRITE_TAC[] THEN
         CONJ_TAC THENL [NONOVERLAPPING_TAC; NONOVERLAPPING_TAC];
         (* pc+108 -> pc+256: CMP X9,X4; BCS forward since X9=niblen>=256 *)
         ENSURES_INIT_TAC "s0" THEN
         SUBGOAL_THEN `256 <= val(word niblen:int64)` ASSUME_TAC THENL
          [REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN
           SUBGOAL_THEN `niblen MOD 18446744073709551616 = niblen`
            SUBST1_TAC THENL
            [MATCH_MP_TAC MOD_LT THEN UNDISCH_TAC `niblen < 272` THEN
             ARITH_TAC;
             ASM_REWRITE_TAC[]];
           ALL_TAC] THEN
         ARM_STEPS_TAC MLDSA_REJ_UNIFORM_ETA4_EXEC (1--2) THEN
         ENSURES_FINAL_STATE_TAC THEN
         REWRITE_TAC[ALL] THEN ASM_REWRITE_TAC[] THEN
         EXISTS_TAC `N:num` THEN
         CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN ASM_REWRITE_TAC[] THEN
         UNDISCH_TAC `niblen < 272` THEN EXPAND_TAC "niblen" THEN
         ARITH_TAC];
       (* Subcase: X2 < 8 — falls through *)
       ENSURES_INIT_TAC "s0" THEN
       ARM_STEPS_TAC MLDSA_REJ_UNIFORM_ETA4_EXEC (1--2) THEN
       ENSURES_FINAL_STATE_TAC THEN
       REWRITE_TAC[ALL] THEN ASM_REWRITE_TAC[] THEN
       EXISTS_TAC `N:num` THEN
       CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN ASM_REWRITE_TAC[] THEN
       UNDISCH_TAC `niblen < 272` THEN EXPAND_TAC "niblen" THEN
       ARITH_TAC];
     (* Case: ~(256 <= niblen) — buffer exhausted *)
     SUBGOAL_THEN `buflen < 8 * (N + 1)` ASSUME_TAC THENL
      [FIRST_X_ASSUM(DISJ_CASES_THEN ASSUME_TAC) THEN ASM_REWRITE_TAC[] THEN
       UNDISCH_TAC `~(256 <= niblen)` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
     SUBGOAL_THEN `8 * N <= buflen` ASSUME_TAC THENL
      [FIRST_X_ASSUM(MP_TAC o SPEC `N - 1`) THEN
       UNDISCH_TAC `0 < N` THEN ARITH_TAC; ALL_TAC] THEN
     SUBGOAL_THEN `8 * N = buflen` ASSUME_TAC THENL
      [MP_TAC(ASSUME `8 divides buflen`) THEN
       REWRITE_TAC[divides] THEN
       DISCH_THEN(X_CHOOSE_TAC `d:num`) THEN ASM_REWRITE_TAC[] THEN
       UNDISCH_TAC `buflen < 8 * (N + 1)` THEN ASM_REWRITE_TAC[] THEN
       UNDISCH_TAC `8 * N <= buflen` THEN ASM_REWRITE_TAC[] THEN
       REWRITE_TAC[GSYM MULT_ASSOC; LT_MULT_LCANCEL; LE_MULT_LCANCEL] THEN
       CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC; ALL_TAC] THEN
     SUBGOAL_THEN `SUB_LIST(0,buflen) inlist = inlist:byte list`
       (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
      [MATCH_MP_TAC SUB_LIST_REFL THEN ASM_REWRITE_TAC[LE_REFL]; ALL_TAC] THEN
     ASM_REWRITE_TAC[] THEN
     SUBGOAL_THEN `~(8 <= val(word_sub (word buflen:int64) (word buflen)))`
       ASSUME_TAC THENL
      [REWRITE_TAC[WORD_SUB_REFL; VAL_WORD_0] THEN ARITH_TAC; ALL_TAC] THEN
     ENSURES_INIT_TAC "s0" THEN
     ARM_STEPS_TAC MLDSA_REJ_UNIFORM_ETA4_EXEC (1--2) THEN
     ENSURES_FINAL_STATE_TAC THEN
     REWRITE_TAC[ALL] THEN ASM_REWRITE_TAC[] THEN
     EXISTS_TAC `N:num` THEN
     CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN ASM_REWRITE_TAC[] THEN
     CONJ_TAC THENL
      [UNDISCH_TAC `niblen < 272` THEN EXPAND_TAC "niblen" THEN
       ARITH_TAC; ALL_TAC] THEN
     CONJ_TAC THENL
      [DISJ1_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
     ASM_REWRITE_TAC[]]]);;
