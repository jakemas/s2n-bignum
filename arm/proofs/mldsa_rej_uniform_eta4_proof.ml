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
(* 4-byte variant: bridge between 8-halfword bitval sum and             *)
(* LENGTH(REJ_NIBBLES_ETA4 [b0;b1;b2;b3]). Used for the per-half         *)
(* X12 / X13 popcount equalities in the first-half TBL existential.     *)
let COUNT_BRIDGE_ABSTRACT_4 = prove(
  `!x0:int128. !b0 b1 b2 b3:byte.
      word_subword x0 (0,16):int16 = word_zx(word_and b0 (word 15):byte):int16 /\
      word_subword x0 (16,16):int16 = word_zx(word_ushr b0 4:byte):int16 /\
      word_subword x0 (32,16):int16 = word_zx(word_and b1 (word 15):byte):int16 /\
      word_subword x0 (48,16):int16 = word_zx(word_ushr b1 4:byte):int16 /\
      word_subword x0 (64,16):int16 = word_zx(word_and b2 (word 15):byte):int16 /\
      word_subword x0 (80,16):int16 = word_zx(word_ushr b2 4:byte):int16 /\
      word_subword x0 (96,16):int16 = word_zx(word_and b3 (word 15):byte):int16 /\
      word_subword x0 (112,16):int16 = word_zx(word_ushr b3 4:byte):int16
      ==>
      bitval(val(word_subword x0 (0,16):int16) < 9) +
      bitval(val(word_subword x0 (16,16):int16) < 9) +
      bitval(val(word_subword x0 (32,16):int16) < 9) +
      bitval(val(word_subword x0 (48,16):int16) < 9) +
      bitval(val(word_subword x0 (64,16):int16) < 9) +
      bitval(val(word_subword x0 (80,16):int16) < 9) +
      bitval(val(word_subword x0 (96,16):int16) < 9) +
      bitval(val(word_subword x0 (112,16):int16) < 9) =
      LENGTH(REJ_NIBBLES_ETA4 [b0;b1;b2;b3])`,
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN SUBST1_TAC) THEN
  REWRITE_TAC[REJ_NIBBLES_ETA4; REJ_NIBBLES_COUNT_4] THEN
  REWRITE_TAC[VAL_WORD_ZX_BYTE16; BYTE_AND_15_MOD; BYTE_USHR4_DIV] THEN
  ARITH_TAC);;

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

(* Byte-split lemmas used in the TBL correctness inline proof.  For each
   halfword position k*16 (k=0..7), derive byte-level identities from the
   halfword identity `word_subword x (k*16,16):int16 = word_zx(b):int16`:
     word_subword x (k*16,8):byte = b (low byte)
     word_subword x (k*16+8,8):byte = word 0 (high byte, since b is int8)
   These let WORD_BLAST close the TBL leaf cases where the TBL output picks
   byte positions at (k*16,8) or (k*16+8,8) of nibbles0/nibbles1b. *)
let BYTE_SPLIT_AND = map (fun k ->
    BITBLAST_RULE(parse_term(Printf.sprintf
     "!x:int128 b:byte. \
       word_subword x (%d,16):int16 = word_zx(word_and b (word 15):byte):int16 \
       ==> word_subword x (%d,8):byte = word_and b (word 15):byte /\\ \
           word_subword x (%d,8):byte = word 0:byte"
     (k*16) (k*16) (k*16+8))))
  (0--7);;

(* For any byte b, val b DIV/MOD 16 is < 16 < 65536, so the MOD 65536 is
   a no-op.  Used in the TBL correctness closure where FILTER produces
   `word(val b DIV 16 MOD 65536):int16` on RHS, and WORD_BLAST needs
   `word(val b DIV 16):int16` to match the LHS. *)
let VAL_BYTE_NIB_MOD_65536 = prove(
  `!b:byte. (val b DIV 16) MOD 65536 = val b DIV 16 /\
            val b MOD 16 MOD 65536 = val b MOD 16`,
  GEN_TAC THEN CONJ_TAC THEN MATCH_MP_TAC MOD_LT THEN
  MP_TAC(ISPEC `b:byte` VAL_BOUND) THEN REWRITE_TAC[DIMINDEX_8] THEN ARITH_TAC);;

let BYTE_SPLIT_USHR = map (fun k ->
    BITBLAST_RULE(parse_term(Printf.sprintf
     "!x:int128 b:byte. \
       word_subword x (%d,16):int16 = word_zx(word_ushr b 4:byte):int16 \
       ==> word_subword x (%d,8):byte = word_ushr b 4:byte /\\ \
           word_subword x (%d,8):byte = word 0:byte"
     (k*16) (k*16) (k*16+8))))
  (0--7);;

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
(* Bound lemma for REJ_NIBBLES_ETA4 on an 8-byte (one-byte-list) chunk.       *)
(* The first/second 4-byte halves each produce at most 8 half-nibbles.        *)
(* ========================================================================= *)

let REJ_NIBBLES_ETA4_LENGTH_4 = prove
 (`!b0 b1 b2 b3:byte.
     LENGTH(REJ_NIBBLES_ETA4 [b0;b1;b2;b3]:int16 list) <= 8`,
  REPEAT GEN_TAC THEN REWRITE_TAC[REJ_NIBBLES_ETA4] THEN
  W(MP_TAC o PART_MATCH lhand LENGTH_FILTER o lhand o snd) THEN
  REWRITE_TAC[NIBBLES_OF_BYTES; NIBBLE_PAIR; APPEND; LENGTH] THEN
  ARITH_TAC);;

(* ========================================================================= *)
(* TBL correctness for the eta4 rejection sampling.                           *)
(*                                                                            *)
(* CONTRACT LEMMA: at the end of the first-half 29-step SIMD chain, the       *)
(* Q16/Q17/X12/X13 register values form a valid witness for the existential  *)
(* invariant `?lis0 lis1. ... APPEND lis0 lis1 = REJ_NIBBLES_ETA4 (bytes of   *)
(* d) /\ read Q16 s = word(num_of_wordlist lis0) /\ read Q17 s = word(...)`. *)
(*                                                                            *)
(* The statement below captures the `REJ_NIBBLES_ETA4` half-decomposition    *)
(* — the actual SIMD-state-to-witness connection is CHEATed at the proof's   *)
(* first-half branch (line 986). Closing this obligation requires expanding  *)
(* the 256-entry eta table via BYTES_EQ_NUM_OF_WORDLIST_EXPAND_CONV and a    *)
(* brute-force case analysis over the popcount index, following the pattern  *)
(* at mldsa_rej_uniform.ml:869-923.                                           *)
(* ========================================================================= *)

(* Prefix lemma: REJ_SAMPLE_ETA4(SUB_LIST(0,k) l) is a prefix of
   REJ_SAMPLE_ETA4 l (via APPEND decomposition of SUB_LIST). *)
(* BYTES128_TO_WORDLIST: a single bytes128 read equals num_of_wordlist of 4 int32s.
   Useful for converting per-16-byte chunk hyps into standard bytes form. *)
let BYTES128_TO_WORDLIST = prove
 (`!s:armstate a:int64 (ws:int32 list).
    LENGTH ws = 4 /\
    read (memory :> bytes128 a) s = word (num_of_wordlist ws)
    ==>
    read (memory :> bytes (a,16)) s = num_of_wordlist ws`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o AP_TERM `val:int128->num`) THEN
  REWRITE_TAC[READ_COMPONENT_COMPOSE; BYTES128_WBYTES; VAL_READ_WBYTES;
              DIMINDEX_128; ARITH_RULE `128 DIV 8 = 16`] THEN
  DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[VAL_WORD; DIMINDEX_128] THEN
  MATCH_MP_TAC MOD_LT THEN
  MATCH_MP_TAC NUM_OF_WORDLIST_BOUND_GEN THEN
  REWRITE_TAC[DIMINDEX_32] THEN
  ASM_REWRITE_TAC[] THEN ARITH_TAC);;

(* BYTES_APPEND_WORDLISTS: chain two adjacent bytes-equal-num_of_wordlist
   facts into one covering the union. Direct wrapper around
   BYTES_EQ_NUM_OF_WORDLIST_APPEND. *)
let BYTES_APPEND_WORDLISTS = prove
 (`!s:armstate a:int64 (l1:(N word)list) (l2:(N word)list) n1 n2.
    dimindex(:N) * LENGTH l1 = 8 * n1 /\
    read (memory :> bytes (a, n1)) s = num_of_wordlist l1 /\
    read (memory :> bytes (word_add a (word n1), n2)) s = num_of_wordlist l2
    ==>
    read (memory :> bytes (a, n1 + n2)) s = num_of_wordlist (APPEND l1 l2)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`memory:(armstate,(64)word->(8)word)component`;
                 `a:int64`; `s:armstate`; `l1:(N word)list`; `l2:(N word)list`;
                 `n1:num`; `n2:num`] BYTES_EQ_NUM_OF_WORDLIST_APPEND) THEN
  ASM_REWRITE_TAC[]);;

(* MEM_1024_TO_SUB_LIST_CASE_A/B/FINAL: bridges the raw memory equation
   (for one of two cases) to the truncated form
   `read(bytes(res, 4*MIN 256 outlen)) s = num_of_wordlist(SUB_LIST(0,256) outlist)`
   needed at the writeback postcondition. *)
let MEM_1024_TO_SUB_LIST_CASE_A = prove
 (`!s:armstate res:int64 outlen:num (outlist:int32 list).
    outlen <= 256 /\
    LENGTH outlist = outlen /\
    read (memory :> bytes (res, 4 * outlen)) s =
    num_of_wordlist outlist
    ==>
    read (memory :> bytes (res,4 * MIN 256 outlen)) s =
    num_of_wordlist (SUB_LIST (0,256) outlist)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `MIN 256 outlen = outlen` SUBST1_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `SUB_LIST(0,256) (outlist:int32 list) = outlist` SUBST1_TAC THENL
   [MATCH_MP_TAC SUB_LIST_REFL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[]);;

let MEM_1024_TO_SUB_LIST_CASE_B = prove
 (`!s:armstate res:int64 outlen:num (outlist:int32 list).
    256 <= outlen /\
    read (memory :> bytes (res,1024)) s =
    num_of_wordlist (SUB_LIST (0,256) outlist:int32 list)
    ==>
    read (memory :> bytes (res,4 * MIN 256 outlen)) s =
    num_of_wordlist (SUB_LIST (0,256) outlist)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `MIN 256 outlen = 256` SUBST1_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[ARITH_RULE `4 * 256 = 1024`]);;

let MEM_1024_TO_SUB_LIST_FINAL = prove
 (`!s:armstate res:int64 outlen:num (outlist:int32 list).
    LENGTH outlist = outlen /\
    (outlen <= 256 /\
     read (memory :> bytes (res, 4 * outlen)) s =
     num_of_wordlist outlist \/
     256 <= outlen /\
     read (memory :> bytes (res,1024)) s =
     num_of_wordlist (SUB_LIST (0,256) outlist))
    ==>
    read (memory :> bytes (res,4 * MIN 256 outlen)) s =
    num_of_wordlist (SUB_LIST (0,256) outlist)`,
  REPEAT STRIP_TAC THENL
   [MATCH_MP_TAC MEM_1024_TO_SUB_LIST_CASE_A THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC MEM_1024_TO_SUB_LIST_CASE_B THEN ASM_REWRITE_TAC[]]);;

(* SSHLL_CHUNK_FROM_INT128_LO/HI: per-chunk BITBLAST reductions matching the exact   *)
(* form the ARM writeback emits. After ARM_STEPS, each bytes128 hyp at res+16j       *)
(* has the form:                                                                     *)
(*   word_join (word_join (word_shl (word_sx (word_subword (word_subword             *)
(*     <packed-SUB-vector> (p,64)) (r,16))) 0) ...)                                  *)
(* where <packed-SUB-vector> is an int128 built from `word_sub (word 4) ...` of      *)
(* halfwords of `c = word_join b_{2k+1} b_{2k}`, and p = 0 (j even) or 64 (j odd).   *)
(* These two identities collapse the full composite to a clean                        *)
(*   word_join (word_join (word_sx(word_sub (word 4) (word_subword c (q,16)))) ...) *)
(* form that matches num_of_wordlist of 4 int32s — directly usable with              *)
(* BYTES128_TO_WORDLIST and BYTES_APPEND_WORDLISTS. *)

let SSHLL_CHUNK_FROM_INT128_LO = BITBLAST_RULE
 `word_join (word_join
    (word_shl (word_sx (word_subword (word_subword (word_join (word_join (word_join
       (word_sub (word 4:int16) (word_subword (c:int128) (112,16):int16):int16)
       (word_sub (word 4:int16) (word_subword c (96,16):int16):int16):int32)
      (word_join (word_sub (word 4:int16) (word_subword c (80,16):int16):int16)
       (word_sub (word 4:int16) (word_subword c (64,16):int16):int16):int32):int64)
     (word_join (word_join
       (word_sub (word 4:int16) (word_subword c (48,16):int16):int16)
       (word_sub (word 4:int16) (word_subword c (32,16):int16):int16):int32)
      (word_join (word_sub (word 4:int16) (word_subword c (16,16):int16):int16)
       (word_sub (word 4:int16) (word_subword c (0,16):int16):int16):int32):int64)
     :int128) (0,64):int64) (48,16):int16):int32) 0)
    (word_shl (word_sx (word_subword (word_subword (word_join (word_join (word_join
       (word_sub (word 4:int16) (word_subword c (112,16):int16):int16)
       (word_sub (word 4:int16) (word_subword c (96,16):int16):int16):int32)
      (word_join (word_sub (word 4:int16) (word_subword c (80,16):int16):int16)
       (word_sub (word 4:int16) (word_subword c (64,16):int16):int16):int32):int64)
     (word_join (word_join
       (word_sub (word 4:int16) (word_subword c (48,16):int16):int16)
       (word_sub (word 4:int16) (word_subword c (32,16):int16):int16):int32)
      (word_join (word_sub (word 4:int16) (word_subword c (16,16):int16):int16)
       (word_sub (word 4:int16) (word_subword c (0,16):int16):int16):int32):int64)
     :int128) (0,64):int64) (32,16):int16):int32) 0):int64)
   (word_join
    (word_shl (word_sx (word_subword (word_subword (word_join (word_join (word_join
       (word_sub (word 4:int16) (word_subword c (112,16):int16):int16)
       (word_sub (word 4:int16) (word_subword c (96,16):int16):int16):int32)
      (word_join (word_sub (word 4:int16) (word_subword c (80,16):int16):int16)
       (word_sub (word 4:int16) (word_subword c (64,16):int16):int16):int32):int64)
     (word_join (word_join
       (word_sub (word 4:int16) (word_subword c (48,16):int16):int16)
       (word_sub (word 4:int16) (word_subword c (32,16):int16):int16):int32)
      (word_join (word_sub (word 4:int16) (word_subword c (16,16):int16):int16)
       (word_sub (word 4:int16) (word_subword c (0,16):int16):int16):int32):int64)
     :int128) (0,64):int64) (16,16):int16):int32) 0)
    (word_shl (word_sx (word_subword (word_subword (word_join (word_join (word_join
       (word_sub (word 4:int16) (word_subword c (112,16):int16):int16)
       (word_sub (word 4:int16) (word_subword c (96,16):int16):int16):int32)
      (word_join (word_sub (word 4:int16) (word_subword c (80,16):int16):int16)
       (word_sub (word 4:int16) (word_subword c (64,16):int16):int16):int32):int64)
     (word_join (word_join
       (word_sub (word 4:int16) (word_subword c (48,16):int16):int16)
       (word_sub (word 4:int16) (word_subword c (32,16):int16):int16):int32)
      (word_join (word_sub (word 4:int16) (word_subword c (16,16):int16):int16)
       (word_sub (word 4:int16) (word_subword c (0,16):int16):int16):int32):int64)
     :int128) (0,64):int64) (0,16):int16):int32) 0):int64):int128 =
  word_join
   (word_join (word_sx(word_sub (word 4:int16) (word_subword c (48,16):int16)):int32)
              (word_sx(word_sub (word 4:int16) (word_subword c (32,16):int16)):int32):int64)
   (word_join (word_sx(word_sub (word 4:int16) (word_subword c (16,16):int16)):int32)
              (word_sx(word_sub (word 4:int16) (word_subword c (0,16):int16)):int32):int64)
   :int128`;;

let SSHLL_CHUNK_FROM_INT128_HI = BITBLAST_RULE
 `word_join (word_join
    (word_shl (word_sx (word_subword (word_subword (word_join (word_join (word_join
       (word_sub (word 4:int16) (word_subword (c:int128) (112,16):int16):int16)
       (word_sub (word 4:int16) (word_subword c (96,16):int16):int16):int32)
      (word_join (word_sub (word 4:int16) (word_subword c (80,16):int16):int16)
       (word_sub (word 4:int16) (word_subword c (64,16):int16):int16):int32):int64)
     (word_join (word_join
       (word_sub (word 4:int16) (word_subword c (48,16):int16):int16)
       (word_sub (word 4:int16) (word_subword c (32,16):int16):int16):int32)
      (word_join (word_sub (word 4:int16) (word_subword c (16,16):int16):int16)
       (word_sub (word 4:int16) (word_subword c (0,16):int16):int16):int32):int64)
     :int128) (64,64):int64) (48,16):int16):int32) 0)
    (word_shl (word_sx (word_subword (word_subword (word_join (word_join (word_join
       (word_sub (word 4:int16) (word_subword c (112,16):int16):int16)
       (word_sub (word 4:int16) (word_subword c (96,16):int16):int16):int32)
      (word_join (word_sub (word 4:int16) (word_subword c (80,16):int16):int16)
       (word_sub (word 4:int16) (word_subword c (64,16):int16):int16):int32):int64)
     (word_join (word_join
       (word_sub (word 4:int16) (word_subword c (48,16):int16):int16)
       (word_sub (word 4:int16) (word_subword c (32,16):int16):int16):int32)
      (word_join (word_sub (word 4:int16) (word_subword c (16,16):int16):int16)
       (word_sub (word 4:int16) (word_subword c (0,16):int16):int16):int32):int64)
     :int128) (64,64):int64) (32,16):int16):int32) 0):int64)
   (word_join
    (word_shl (word_sx (word_subword (word_subword (word_join (word_join (word_join
       (word_sub (word 4:int16) (word_subword c (112,16):int16):int16)
       (word_sub (word 4:int16) (word_subword c (96,16):int16):int16):int32)
      (word_join (word_sub (word 4:int16) (word_subword c (80,16):int16):int16)
       (word_sub (word 4:int16) (word_subword c (64,16):int16):int16):int32):int64)
     (word_join (word_join
       (word_sub (word 4:int16) (word_subword c (48,16):int16):int16)
       (word_sub (word 4:int16) (word_subword c (32,16):int16):int16):int32)
      (word_join (word_sub (word 4:int16) (word_subword c (16,16):int16):int16)
       (word_sub (word 4:int16) (word_subword c (0,16):int16):int16):int32):int64)
     :int128) (64,64):int64) (16,16):int16):int32) 0)
    (word_shl (word_sx (word_subword (word_subword (word_join (word_join (word_join
       (word_sub (word 4:int16) (word_subword c (112,16):int16):int16)
       (word_sub (word 4:int16) (word_subword c (96,16):int16):int16):int32)
      (word_join (word_sub (word 4:int16) (word_subword c (80,16):int16):int16)
       (word_sub (word 4:int16) (word_subword c (64,16):int16):int16):int32):int64)
     (word_join (word_join
       (word_sub (word 4:int16) (word_subword c (48,16):int16):int16)
       (word_sub (word 4:int16) (word_subword c (32,16):int16):int16):int32)
      (word_join (word_sub (word 4:int16) (word_subword c (16,16):int16):int16)
       (word_sub (word 4:int16) (word_subword c (0,16):int16):int16):int32):int64)
     :int128) (64,64):int64) (0,16):int16):int32) 0):int64):int128 =
  word_join
   (word_join (word_sx(word_sub (word 4:int16) (word_subword c (112,16):int16)):int32)
              (word_sx(word_sub (word 4:int16) (word_subword c (96,16):int16)):int32):int64)
   (word_join (word_sx(word_sub (word 4:int16) (word_subword c (80,16):int16)):int32)
              (word_sx(word_sub (word 4:int16) (word_subword c (64,16):int16)):int32):int64)
   :int128`;;

(* Zero-tail helpers for the writeback phase.                                       *)
(* NUM_OF_WORDLIST_REPLICATE_0 / BYTES_APPEND_ZEROS: used to combine the live        *)
(* "bytes(sp, 2*niblen) = num_of_wordlist niblist" with an implied zero-tail         *)
(* "bytes(sp+2*niblen, 512-2*niblen) = 0" into a single 512-byte-stack statement:   *)
(*   bytes(sp, 512) = num_of_wordlist(APPEND niblist (REPLICATE (256-niblen) 0)).    *)
(* REPLICATE_ADD / SUB_LIST_APPEND_SHIFT: list-manipulation helpers.                  *)
(* STACK_CONTENT / LENGTH_STACK_CONTENT / STACK_CONTENT_SMALL/_LARGE: the unified   *)
(*   256-entry stack abstraction that handles both niblen<=256 and niblen>256 cases. *)
(* This strengthened stack invariant will be needed to close the writeback CHEAT     *)
(* by expressing all 64 int64 chunks b_0..b_63 as the 256-wordlist derived from      *)
(* STACK_CONTENT niblist. *)

let NUM_OF_WORDLIST_REPLICATE_0 = prove
 (`!n:num. num_of_wordlist (REPLICATE n (word 0:N word)) = 0`,
  INDUCT_TAC THEN ASM_REWRITE_TAC[REPLICATE; num_of_wordlist;
    VAL_WORD_0; MULT_CLAUSES; ADD_CLAUSES]);;

let BYTES_APPEND_ZEROS = prove
 (`!(m:(S,(64)word->(8)word)component) (s:S)
    (a:int64) (lis1:(N word)list) k1 k2 n2.
    dimindex(:N) * LENGTH lis1 = 8 * k1 /\
    read (m :> bytes (a, k1)) s = num_of_wordlist lis1 /\
    read (m :> bytes (word_add a (word k1), k2)) s = 0
    ==>
    read (m :> bytes (a, k1 + k2)) s =
    num_of_wordlist (APPEND lis1 (REPLICATE n2 (word 0:N word)))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`m:(S,(64)word->(8)word)component`;
                 `a:int64`; `s:S`;
                 `lis1:(N word)list`;
                 `REPLICATE n2 (word 0:N word)`;
                 `k1:num`; `k2:num`] BYTES_EQ_NUM_OF_WORDLIST_APPEND) THEN
  ASM_REWRITE_TAC[NUM_OF_WORDLIST_REPLICATE_0]);;

let REPLICATE_ADD = prove
 (`!m n (x:A). REPLICATE (m + n) x = APPEND (REPLICATE m x) (REPLICATE n x)`,
  INDUCT_TAC THEN ASM_REWRITE_TAC[REPLICATE; ADD_CLAUSES; APPEND]);;

let SUB_LIST_APPEND_SHIFT = prove
 (`!(l1:A list) l2 m.
     SUB_LIST(0, LENGTH l1 + m) (APPEND l1 l2) =
     APPEND l1 (SUB_LIST(0, m) l2)`,
  LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[APPEND; LENGTH; ADD_CLAUSES; SUB_LIST_CLAUSES]);;

let STACK_CONTENT = define
 `STACK_CONTENT (niblist:int16 list) =
    SUB_LIST(0, 256) (APPEND niblist (REPLICATE 256 (word 0:int16)))`;;

let LENGTH_STACK_CONTENT = prove
 (`!niblist:int16 list. LENGTH (STACK_CONTENT niblist) = 256`,
  REWRITE_TAC[STACK_CONTENT; LENGTH_SUB_LIST; LENGTH_APPEND;
              LENGTH_REPLICATE; SUB_0] THEN
  REWRITE_TAC[ARITH_RULE `MIN 256 x = x <=> x <= 256`;
              ARITH_RULE `MIN 256 x = 256 <=> 256 <= x`] THEN
  ARITH_TAC);;

let STACK_CONTENT_SMALL = prove
 (`!niblist:int16 list.
     LENGTH niblist <= 256
     ==> STACK_CONTENT niblist =
         APPEND niblist (REPLICATE (256 - LENGTH niblist) (word 0:int16))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[STACK_CONTENT] THEN
  MP_TAC(ISPECL [`niblist:int16 list`; `REPLICATE 256 (word 0:int16)`;
                 `256 - LENGTH(niblist:int16 list)`] SUB_LIST_APPEND_SHIFT) THEN
  SUBGOAL_THEN `LENGTH(niblist:int16 list) + 256 - LENGTH niblist = 256`
    SUBST1_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN SUBST1_TAC THEN AP_TERM_TAC THEN
  ABBREV_TAC `pad:num = 256 - LENGTH(niblist:int16 list)` THEN
  SUBGOAL_THEN `256 = pad + (256 - pad)` SUBST1_TAC THENL
   [EXPAND_TAC "pad" THEN ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[REPLICATE_ADD] THEN
  MP_TAC(ISPECL [`REPLICATE pad (word 0:int16)`;
                 `REPLICATE (256 - pad) (word 0:int16)`;
                 `pad:num`] SUB_LIST_APPEND_LEFT) THEN
  REWRITE_TAC[LENGTH_REPLICATE; LE_REFL] THEN DISCH_THEN SUBST1_TAC THEN
  MATCH_MP_TAC SUB_LIST_REFL THEN REWRITE_TAC[LENGTH_REPLICATE; LE_REFL]);;

let STACK_CONTENT_LARGE = prove
 (`!niblist:int16 list.
     256 <= LENGTH niblist
     ==> STACK_CONTENT niblist = SUB_LIST(0, 256) niblist`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[STACK_CONTENT] THEN
  MATCH_MP_TAC SUB_LIST_APPEND_LEFT THEN ASM_REWRITE_TAC[]);;

(* WORD_NUM_OF_WORDLIST_PAD_ZEROS: the Q register value word(num_of_wordlist lis)  *)
(* where LENGTH lis <= 8 has zero high bits, so equals                             *)
(* word(num_of_wordlist (APPEND lis (REPLICATE (8 - LENGTH lis) 0))).              *)
(* Used to convert the ARM loop body's Q16/Q17 store values into their             *)
(* zero-padded 8-halfword form, matching the STACK_CONTENT update formula.         *)

let WORD_NUM_OF_WORDLIST_PAD_ZEROS = prove
 (`!lis0:int16 list.
     LENGTH lis0 <= 8
     ==> word(num_of_wordlist lis0):int128 =
         word(num_of_wordlist (APPEND lis0
              (REPLICATE (8 - LENGTH lis0) (word 0:int16))))`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[NUM_OF_WORDLIST_APPEND; NUM_OF_WORDLIST_REPLICATE_0] THEN
  REWRITE_TAC[DIMINDEX_16; MULT_CLAUSES; ADD_CLAUSES]);;

(* BYTES128_TO_WORDLIST_INT16: converts read(bytes128 a) s = word(num_of_wordlist ws) *)
(* (where ws:int16 list of LENGTH 8) into the bytes/num_of_wordlist form.              *)

let BYTES128_TO_WORDLIST_INT16 = prove
 (`!s:armstate a:int64 (ws:int16 list).
    LENGTH ws = 8 /\
    read (memory :> bytes128 a) s = word (num_of_wordlist ws)
    ==>
    read (memory :> bytes (a,16)) s = num_of_wordlist ws`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o AP_TERM `val:int128->num`) THEN
  REWRITE_TAC[READ_COMPONENT_COMPOSE; BYTES128_WBYTES; VAL_READ_WBYTES;
              DIMINDEX_128; ARITH_RULE `128 DIV 8 = 16`] THEN
  DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[VAL_WORD; DIMINDEX_128] THEN
  MATCH_MP_TAC MOD_LT THEN
  MATCH_MP_TAC NUM_OF_WORDLIST_BOUND_GEN THEN
  REWRITE_TAC[DIMINDEX_16] THEN
  ASM_REWRITE_TAC[] THEN ARITH_TAC);;

(* BYTES_APPEND_BYTES128: combine a bytes region holding num_of_wordlist lis1     *)
(* with an adjacent bytes128 holding word(num_of_wordlist lis2) where LENGTH lis2 = 8. *)
(* Yields: read(bytes(a, k+16)) s = num_of_wordlist (APPEND lis1 lis2). *)

let BYTES_APPEND_BYTES128 = prove
 (`!(s:armstate) (a:int64) (lis1:int16 list) (lis2:int16 list) k.
    2 * LENGTH lis1 = k /\
    LENGTH lis2 = 8 /\
    read (memory :> bytes (a, k)) s = num_of_wordlist lis1 /\
    read (memory :> bytes128 (word_add a (word k))) s =
    word (num_of_wordlist lis2)
    ==>
    read (memory :> bytes (a, k + 16)) s =
    num_of_wordlist (APPEND lis1 lis2)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`memory:(armstate,(64)word->(8)word)component`;
                 `a:int64`; `s:armstate`;
                 `lis1:int16 list`; `lis2:int16 list`;
                 `k:num`; `16:num`] BYTES_EQ_NUM_OF_WORDLIST_APPEND) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[DIMINDEX_16] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC BYTES128_TO_WORDLIST_INT16 THEN ASM_REWRITE_TAC[]);;

(* F_OF_ZERO, MAP_REPLICATE, MAP_F_REJ_NIBBLES, DERIVED_OUTPUT_SMALL/LARGE:       *)
(* the final bridge family connecting the MAP of our SSHLL-semantic function f     *)
(* (f x = word_sx(word_sub (word 4) x):int32) over STACK_CONTENT niblist to the   *)
(* REJ_SAMPLE_ETA4 output, with zero-pad extension for the small-niblen case.      *)

let F_OF_ZERO = BITBLAST_RULE
 `word_sx(word_sub (word 4:int16) (word 0:int16)):int32 = word 4:int32`;;

let MAP_REPLICATE = prove
 (`!(f:A->B) n x. MAP f (REPLICATE n x) = REPLICATE n (f x)`,
  GEN_TAC THEN INDUCT_TAC THEN ASM_REWRITE_TAC[REPLICATE; MAP]);;

let DERIVED_OUTPUT_SMALL = prove
 (`!(niblist:int16 list).
     LENGTH niblist <= 256
     ==> MAP (\x. word_sx(word_sub (word 4:int16) x):int32)
              (STACK_CONTENT niblist) =
         APPEND (MAP (\x. word_sx(word_sub (word 4:int16) x):int32) niblist)
                (REPLICATE (256 - LENGTH niblist) (word 4:int32))`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[STACK_CONTENT_SMALL; MAP_APPEND; MAP_REPLICATE] THEN
  REWRITE_TAC[F_OF_ZERO]);;

let DERIVED_OUTPUT_LARGE = prove
 (`!(niblist:int16 list).
     256 <= LENGTH niblist
     ==> MAP (\x. word_sx(word_sub (word 4:int16) x):int32)
              (STACK_CONTENT niblist) =
         SUB_LIST(0, 256)
           (MAP (\x. word_sx(word_sub (word 4:int16) x):int32) niblist)`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[STACK_CONTENT_LARGE; GSYM SUB_LIST_MAP]);;

let MAP_F_REJ_NIBBLES = prove
 (`!l:byte list.
     MAP (\x. word_sx(word_sub (word 4:int16) x):int32)
         (REJ_NIBBLES_ETA4 l) =
     REJ_SAMPLE_ETA4 l`,
  REWRITE_TAC[REJ_SAMPLE_ETA4]);;

(* WORD_OF_NUM_4INT16: word(num_of_wordlist [h0;h1;h2;h3]):int64 in word_join form. *)

let WORD_OF_NUM_4INT16 = prove
 (`!h0 h1 h2 h3:int16.
     word (num_of_wordlist [h0;h1;h2;h3]):int64 =
     word_join (word_join h3 h2:int32) (word_join h1 h0:int32)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[num_of_wordlist; DIMINDEX_16; MULT_CLAUSES; ADD_CLAUSES] THEN
  REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_JOIN; DIMINDEX_64; DIMINDEX_32;
              DIMINDEX_16; VAL_WORD] THEN
  MP_TAC(ISPEC `h0:int16` VAL_BOUND) THEN
  MP_TAC(ISPEC `h1:int16` VAL_BOUND) THEN
  MP_TAC(ISPEC `h2:int16` VAL_BOUND) THEN
  MP_TAC(ISPEC `h3:int16` VAL_BOUND) THEN
  REWRITE_TAC[DIMINDEX_16] THEN REPEAT DISCH_TAC THEN
  SUBGOAL_THEN `(2 EXP 16 * val(h3:int16) + val(h2:int16)) MOD 2 EXP 32 =
                2 EXP 16 * val h3 + val h2` SUBST1_TAC THENL
   [MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(2 EXP 16 * val(h1:int16) + val(h0:int16)) MOD 2 EXP 32 =
                2 EXP 16 * val h1 + val h0` SUBST1_TAC THENL
   [MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC; ALL_TAC] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN ARITH_TAC);;

(* WORD_SUBWORD_JOIN_NOW_H: extracts the halfwords from word_join b_1 (word(num_of_wordlist [...])). *)

let WORD_SUBWORD_JOIN_NOW_H = prove
 (`!b_1:int64. !h0 h1 h2 h3:int16.
     word_subword (word_join b_1 (word(num_of_wordlist [h0;h1;h2;h3]):int64):int128) (0,16):int16 = h0 /\
     word_subword (word_join b_1 (word(num_of_wordlist [h0;h1;h2;h3]):int64):int128) (16,16):int16 = h1 /\
     word_subword (word_join b_1 (word(num_of_wordlist [h0;h1;h2;h3]):int64):int128) (32,16):int16 = h2 /\
     word_subword (word_join b_1 (word(num_of_wordlist [h0;h1;h2;h3]):int64):int128) (48,16):int16 = h3`,
  REPEAT GEN_TAC THEN REWRITE_TAC[WORD_OF_NUM_4INT16] THEN
  CONV_TAC WORD_BLAST);;

(* EL_SUB_LIST: EL i (SUB_LIST(m,n) l) = EL (m+i) l when i<n and m+i<LENGTH l. *)

let EL_SUB_LIST = prove
 (`!l:(A)list. !m n i:num.
     i < n /\ m + i < LENGTH l
     ==> EL i (SUB_LIST (m,n) l) = EL (m + i) l`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[LENGTH; LT] THEN
  MATCH_MP_TAC num_INDUCTION THEN CONJ_TAC THENL
   [MATCH_MP_TAC num_INDUCTION THEN CONJ_TAC THENL
     [REWRITE_TAC[LT];
      X_GEN_TAC `n:num` THEN DISCH_THEN(K ALL_TAC) THEN
      X_GEN_TAC `i:num` THEN REWRITE_TAC[SUB_LIST; ADD_CLAUSES] THEN
      STRUCT_CASES_TAC (SPEC `i:num` num_CASES) THENL
       [REWRITE_TAC[EL; HD];
        REWRITE_TAC[EL; TL; LT_SUC; LENGTH; ADD_CLAUSES] THEN
        STRIP_TAC THEN
        FIRST_X_ASSUM(MP_TAC o SPECL [`0`; `n:num`; `n':num`]) THEN
        ASM_REWRITE_TAC[ADD_CLAUSES] THEN
        DISCH_THEN MATCH_MP_TAC THEN ASM_ARITH_TAC]];
    X_GEN_TAC `m:num` THEN DISCH_THEN(K ALL_TAC) THEN
    X_GEN_TAC `n:num` THEN X_GEN_TAC `i:num` THEN
    REWRITE_TAC[SUB_LIST; LENGTH; ADD_CLAUSES; EL; TL] THEN
    STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`m:num`; `n:num`; `i:num`]) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_ARITH_TAC]);;

(* SUB_LIST_4_EL: SUB_LIST(k,4) = [EL k; EL(k+1); EL(k+2); EL(k+3)]. *)

let SUB_LIST_4_EL = prove
 (`!l:(A)list. !k:num.
     k + 4 <= LENGTH l
     ==> SUB_LIST(k, 4) l =
         [EL k l; EL (k+1) l; EL (k+2) l; EL (k+3) l]`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[LIST_EQ; LENGTH_SUB_LIST; LENGTH] THEN
  CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  X_GEN_TAC `i:num` THEN
  REWRITE_TAC[ARITH_RULE `SUC(SUC(SUC(SUC 0))) = 4`] THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`l:(A)list`; `k:num`; `4`; `i:num`] EL_SUB_LIST) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  SUBGOAL_THEN
    `!P (a:A) b c d.
       (i = 0 ==> P a) /\ (i = 1 ==> P b) /\
       (i = 2 ==> P c) /\ (i = 3 ==> P d)
       ==> P(EL i [a;b;c;d])`
    (fun th -> MATCH_MP_TAC th) THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN UNDISCH_TAC `i < 4` THEN
    REWRITE_TAC[ARITH_RULE
      `i < 4 <=> i = 0 \/ i = 1 \/ i = 2 \/ i = 3`] THEN
    STRIP_TAC THEN
    ASM_SIMP_TAC[ARITH_RULE `3 = SUC 2 /\ 2 = SUC 1 /\ 1 = SUC 0`;
                 EL; HD; TL];
    REPEAT CONJ_TAC THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[ADD_CLAUSES]]);;

(* WORD_SUBWORD_JOIN_SUB_LIST_H: the key halfword-extraction bridge for       *)
(* Case A. Given a position a in niblist with a+8 <= LENGTH niblist, the     *)
(* word_subword of word_join (word(num_of_wordlist (SUB_LIST(a+4,4) niblist)))*)
(* (word(num_of_wordlist (SUB_LIST(a,4) niblist))) at offset 16k yields      *)
(* EL (a+k) niblist for k in {0,...,7}.                                     *)

let WORD_SUBWORD_JOIN_SUB_LIST_H = prove
 (`!niblist:int16 list. !a:num.
     a + 8 <= LENGTH niblist
     ==>
     word_subword (word_join
       (word(num_of_wordlist(SUB_LIST(a+4,4) niblist)):int64)
       (word(num_of_wordlist(SUB_LIST(a,4) niblist)):int64):int128) (0,16):int16 =
       EL a niblist /\
     word_subword (word_join
       (word(num_of_wordlist(SUB_LIST(a+4,4) niblist)):int64)
       (word(num_of_wordlist(SUB_LIST(a,4) niblist)):int64):int128) (16,16):int16 =
       EL (a+1) niblist /\
     word_subword (word_join
       (word(num_of_wordlist(SUB_LIST(a+4,4) niblist)):int64)
       (word(num_of_wordlist(SUB_LIST(a,4) niblist)):int64):int128) (32,16):int16 =
       EL (a+2) niblist /\
     word_subword (word_join
       (word(num_of_wordlist(SUB_LIST(a+4,4) niblist)):int64)
       (word(num_of_wordlist(SUB_LIST(a,4) niblist)):int64):int128) (48,16):int16 =
       EL (a+3) niblist /\
     word_subword (word_join
       (word(num_of_wordlist(SUB_LIST(a+4,4) niblist)):int64)
       (word(num_of_wordlist(SUB_LIST(a,4) niblist)):int64):int128) (64,16):int16 =
       EL (a+4) niblist /\
     word_subword (word_join
       (word(num_of_wordlist(SUB_LIST(a+4,4) niblist)):int64)
       (word(num_of_wordlist(SUB_LIST(a,4) niblist)):int64):int128) (80,16):int16 =
       EL (a+5) niblist /\
     word_subword (word_join
       (word(num_of_wordlist(SUB_LIST(a+4,4) niblist)):int64)
       (word(num_of_wordlist(SUB_LIST(a,4) niblist)):int64):int128) (96,16):int16 =
       EL (a+6) niblist /\
     word_subword (word_join
       (word(num_of_wordlist(SUB_LIST(a+4,4) niblist)):int64)
       (word(num_of_wordlist(SUB_LIST(a,4) niblist)):int64):int128) (112,16):int16 =
       EL (a+7) niblist`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `a + 4 <= LENGTH(niblist:int16 list) /\
                (a + 4) + 4 <= LENGTH(niblist:int16 list)` STRIP_ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`niblist:int16 list`; `a:num`] SUB_LIST_4_EL) THEN
  MP_TAC(ISPECL [`niblist:int16 list`; `a+4:num`] SUB_LIST_4_EL) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN SUBST1_TAC THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[ARITH_RULE `(a+4)+1 = a+5 /\ (a+4)+2 = a+6 /\ (a+4)+3 = a+7`] THEN
  REWRITE_TAC[WORD_OF_NUM_4INT16] THEN CONV_TAC WORD_BLAST);;

Printf.printf "EL_SUB_LIST / SUB_LIST_4_EL / WORD_SUBWORD_JOIN_SUB_LIST_H proved\n%!";;

(* REJ_SAMPLE_ETA4_SUB_LIST_PREFIX: moved early for forward-reference by
   SUB_LIST_256_PREFIX_LARGE. *)

let REJ_SAMPLE_ETA4_SUB_LIST_PREFIX = prove
 (`!k (l:byte list).
     k <= LENGTH l
     ==> ?rest:int32 list.
         APPEND (REJ_SAMPLE_ETA4 (SUB_LIST (0,k) l)) rest =
         REJ_SAMPLE_ETA4 l`,
  REPEAT STRIP_TAC THEN
  EXISTS_TAC `REJ_SAMPLE_ETA4 (SUB_LIST(k, LENGTH l - k) l):int32 list` THEN
  REWRITE_TAC[REJ_SAMPLE_ETA4; GSYM MAP_APPEND] THEN
  AP_TERM_TAC THEN
  REWRITE_TAC[REJ_NIBBLES_ETA4; GSYM FILTER_APPEND] THEN
  AP_TERM_TAC THEN
  REWRITE_TAC[GSYM NIBBLES_OF_BYTES_APPEND] THEN
  AP_TERM_TAC THEN
  MP_TAC(ISPECL [`l:byte list`; `k:num`] SUB_LIST_TOPSPLIT) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(fun th -> GEN_REWRITE_TAC RAND_CONV [SYM th]) THEN
  REFL_TAC);;

(* SUB_LIST_256_PREFIX_LARGE: when 256 <= niblen (= LENGTH of the processed
   REJ_NIBBLES_ETA4 prefix), SUB_LIST(0,256) of REJ_SAMPLE_ETA4 on the full
   inlist equals SUB_LIST(0,256) of REJ_SAMPLE_ETA4 on just the 8*nn-byte prefix. *)

let SUB_LIST_256_PREFIX_LARGE = prove
 (`!inlist:byte list. !nn:num.
     256 <= LENGTH(REJ_NIBBLES_ETA4(SUB_LIST(0, 8*nn) inlist):int16 list)
     ==>
     SUB_LIST(0,256)(REJ_SAMPLE_ETA4 inlist) =
     SUB_LIST(0,256)(REJ_SAMPLE_ETA4 (SUB_LIST(0, 8*nn) inlist))`,
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `8 * nn <= LENGTH(inlist:byte list)` THENL
   [MP_TAC(ISPECL [`8 * nn:num`; `inlist:byte list`]
                REJ_SAMPLE_ETA4_SUB_LIST_PREFIX) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `rest:int32 list` (fun th ->
      GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [SYM th])) THEN
    MATCH_MP_TAC SUB_LIST_APPEND_LEFT THEN
    REWRITE_TAC[REJ_SAMPLE_ETA4; LENGTH_MAP] THEN ASM_REWRITE_TAC[];
    (* Case: 8*nn > LENGTH inlist. Then SUB_LIST(0, 8*nn) inlist = inlist. *)
    SUBGOAL_THEN `SUB_LIST(0, 8 * nn) (inlist:byte list) = inlist` SUBST1_TAC THENL
     [MATCH_MP_TAC SUB_LIST_REFL THEN ASM_ARITH_TAC;
      REFL_TAC]]);;

(* SUB_LIST_8nn_INLIST: when buflen < 8*(nn+1) and 8 divides buflen,
   SUB_LIST(0, 8*nn) inlist = inlist. *)

let SUB_LIST_8nn_INLIST = prove
 (`!inlist:byte list. !nn:num. !buflen:num.
     8 divides buflen /\
     buflen < 8 * (nn + 1) /\
     LENGTH inlist = buflen
     ==>
     SUB_LIST(0, 8 * nn) inlist = inlist`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC SUB_LIST_REFL THEN
  UNDISCH_TAC `8 divides buflen` THEN REWRITE_TAC[divides] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:num` SUBST_ALL_TAC) THEN
  UNDISCH_TAC `LENGTH(inlist:byte list) = 8 * k` THEN
  DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[LE_MULT_LCANCEL] THEN
  UNDISCH_TAC `8 * k < 8 * (nn + 1)` THEN
  REWRITE_TAC[LT_MULT_LCANCEL] THEN ARITH_TAC);;

(* WORD_JOIN_4_INT32S_EQ_NUM_OF_WORDLIST: word_join ladder of 4 int32s is the     *)
(* canonical word(num_of_wordlist [4 int32s]) form. *)

let WORD_JOIN_4_INT32S_EQ_NUM_OF_WORDLIST = prove
 (`!w0:int32. !w1:int32. !w2:int32. !w3:int32.
     word_join
      (word_join (w3:int32) (w2:int32):int64)
      (word_join (w1:int32) (w0:int32):int64):int128 =
     word (num_of_wordlist [w0; w1; w2; w3])`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[num_of_wordlist; DIMINDEX_32; MULT_CLAUSES; ADD_CLAUSES] THEN
  REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_JOIN; DIMINDEX_64; DIMINDEX_128; VAL_WORD] THEN
  MP_TAC(ISPEC `w0:int32` VAL_BOUND) THEN
  MP_TAC(ISPEC `w1:int32` VAL_BOUND) THEN
  MP_TAC(ISPEC `w2:int32` VAL_BOUND) THEN
  MP_TAC(ISPEC `w3:int32` VAL_BOUND) THEN
  REWRITE_TAC[DIMINDEX_32] THEN REPEAT DISCH_TAC THEN
  SUBGOAL_THEN `(2 EXP 32 * val(w3:int32) + val(w2:int32)) MOD 2 EXP 64 =
                2 EXP 32 * val w3 + val w2` SUBST1_TAC THENL
   [MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(2 EXP 32 * val(w1:int32) + val(w0:int32)) MOD 2 EXP 64 =
                2 EXP 32 * val w1 + val w0` SUBST1_TAC THENL
   [MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC; ALL_TAC] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN ARITH_TAC);;

(* MINI_WRITEBACK_CHUNK_LO: single-chunk end-to-end. Given read(bytes128 res) s =  *)
(* (the complex ARM-emitted SSHLL+SUB composite), conclude                        *)
(* read(bytes(res, 16)) s = num_of_wordlist [4 int32 SSHLL'd halfwords of c].     *)
(* Uses SSHLL_CHUNK_FROM_INT128_LO + WORD_JOIN_4_INT32S_EQ + BYTES128_TO_WORDLIST.*)

let MINI_WRITEBACK_CHUNK_LO = prove
 (`!s:armstate. !res:int64. !c:int128.
    read (memory :> bytes128 res) s =
    word_join (word_join
      (word_shl (word_sx (word_subword (word_subword (word_join (word_join (word_join
         (word_sub (word 4:int16) (word_subword c (112,16):int16):int16)
         (word_sub (word 4:int16) (word_subword c (96,16):int16):int16):int32)
        (word_join (word_sub (word 4:int16) (word_subword c (80,16):int16):int16)
         (word_sub (word 4:int16) (word_subword c (64,16):int16):int16):int32):int64)
       (word_join (word_join
         (word_sub (word 4:int16) (word_subword c (48,16):int16):int16)
         (word_sub (word 4:int16) (word_subword c (32,16):int16):int16):int32)
        (word_join (word_sub (word 4:int16) (word_subword c (16,16):int16):int16)
         (word_sub (word 4:int16) (word_subword c (0,16):int16):int16):int32):int64)
       :int128) (0,64):int64) (48,16):int16):int32) 0)
      (word_shl (word_sx (word_subword (word_subword (word_join (word_join (word_join
         (word_sub (word 4:int16) (word_subword c (112,16):int16):int16)
         (word_sub (word 4:int16) (word_subword c (96,16):int16):int16):int32)
        (word_join (word_sub (word 4:int16) (word_subword c (80,16):int16):int16)
         (word_sub (word 4:int16) (word_subword c (64,16):int16):int16):int32):int64)
       (word_join (word_join
         (word_sub (word 4:int16) (word_subword c (48,16):int16):int16)
         (word_sub (word 4:int16) (word_subword c (32,16):int16):int16):int32)
        (word_join (word_sub (word 4:int16) (word_subword c (16,16):int16):int16)
         (word_sub (word 4:int16) (word_subword c (0,16):int16):int16):int32):int64)
       :int128) (0,64):int64) (32,16):int16):int32) 0):int64)
     (word_join
      (word_shl (word_sx (word_subword (word_subword (word_join (word_join (word_join
         (word_sub (word 4:int16) (word_subword c (112,16):int16):int16)
         (word_sub (word 4:int16) (word_subword c (96,16):int16):int16):int32)
        (word_join (word_sub (word 4:int16) (word_subword c (80,16):int16):int16)
         (word_sub (word 4:int16) (word_subword c (64,16):int16):int16):int32):int64)
       (word_join (word_join
         (word_sub (word 4:int16) (word_subword c (48,16):int16):int16)
         (word_sub (word 4:int16) (word_subword c (32,16):int16):int16):int32)
        (word_join (word_sub (word 4:int16) (word_subword c (16,16):int16):int16)
         (word_sub (word 4:int16) (word_subword c (0,16):int16):int16):int32):int64)
       :int128) (0,64):int64) (16,16):int16):int32) 0)
      (word_shl (word_sx (word_subword (word_subword (word_join (word_join (word_join
         (word_sub (word 4:int16) (word_subword c (112,16):int16):int16)
         (word_sub (word 4:int16) (word_subword c (96,16):int16):int16):int32)
        (word_join (word_sub (word 4:int16) (word_subword c (80,16):int16):int16)
         (word_sub (word 4:int16) (word_subword c (64,16):int16):int16):int32):int64)
       (word_join (word_join
         (word_sub (word 4:int16) (word_subword c (48,16):int16):int16)
         (word_sub (word 4:int16) (word_subword c (32,16):int16):int16):int32)
        (word_join (word_sub (word 4:int16) (word_subword c (16,16):int16):int16)
         (word_sub (word 4:int16) (word_subword c (0,16):int16):int16):int32):int64)
       :int128) (0,64):int64) (0,16):int16):int32) 0):int64):int128
    ==>
    read (memory :> bytes (res, 16)) s =
    num_of_wordlist
      [word_sx(word_sub (word 4:int16) (word_subword c (0,16):int16)):int32;
       word_sx(word_sub (word 4:int16) (word_subword c (16,16):int16)):int32;
       word_sx(word_sub (word 4:int16) (word_subword c (32,16):int16)):int32;
       word_sx(word_sub (word 4:int16) (word_subword c (48,16):int16)):int32]`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC BYTES128_TO_WORDLIST THEN
  REWRITE_TAC[LENGTH] THEN CONJ_TAC THENL [ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[SSHLL_CHUNK_FROM_INT128_LO] THEN
  REWRITE_TAC[WORD_JOIN_4_INT32S_EQ_NUM_OF_WORDLIST]);;

(* MINI_WRITEBACK_CHUNK_HI: companion to _LO for (64,64)-extracting chunks. *)

let MINI_WRITEBACK_CHUNK_HI = prove
 (`!s:armstate. !res:int64. !c:int128.
    read (memory :> bytes128 res) s =
    word_join (word_join
      (word_shl (word_sx (word_subword (word_subword (word_join (word_join (word_join
         (word_sub (word 4:int16) (word_subword c (112,16):int16):int16)
         (word_sub (word 4:int16) (word_subword c (96,16):int16):int16):int32)
        (word_join (word_sub (word 4:int16) (word_subword c (80,16):int16):int16)
         (word_sub (word 4:int16) (word_subword c (64,16):int16):int16):int32):int64)
       (word_join (word_join
         (word_sub (word 4:int16) (word_subword c (48,16):int16):int16)
         (word_sub (word 4:int16) (word_subword c (32,16):int16):int16):int32)
        (word_join (word_sub (word 4:int16) (word_subword c (16,16):int16):int16)
         (word_sub (word 4:int16) (word_subword c (0,16):int16):int16):int32):int64)
       :int128) (64,64):int64) (48,16):int16):int32) 0)
      (word_shl (word_sx (word_subword (word_subword (word_join (word_join (word_join
         (word_sub (word 4:int16) (word_subword c (112,16):int16):int16)
         (word_sub (word 4:int16) (word_subword c (96,16):int16):int16):int32)
        (word_join (word_sub (word 4:int16) (word_subword c (80,16):int16):int16)
         (word_sub (word 4:int16) (word_subword c (64,16):int16):int16):int32):int64)
       (word_join (word_join
         (word_sub (word 4:int16) (word_subword c (48,16):int16):int16)
         (word_sub (word 4:int16) (word_subword c (32,16):int16):int16):int32)
        (word_join (word_sub (word 4:int16) (word_subword c (16,16):int16):int16)
         (word_sub (word 4:int16) (word_subword c (0,16):int16):int16):int32):int64)
       :int128) (64,64):int64) (32,16):int16):int32) 0):int64)
     (word_join
      (word_shl (word_sx (word_subword (word_subword (word_join (word_join (word_join
         (word_sub (word 4:int16) (word_subword c (112,16):int16):int16)
         (word_sub (word 4:int16) (word_subword c (96,16):int16):int16):int32)
        (word_join (word_sub (word 4:int16) (word_subword c (80,16):int16):int16)
         (word_sub (word 4:int16) (word_subword c (64,16):int16):int16):int32):int64)
       (word_join (word_join
         (word_sub (word 4:int16) (word_subword c (48,16):int16):int16)
         (word_sub (word 4:int16) (word_subword c (32,16):int16):int16):int32)
        (word_join (word_sub (word 4:int16) (word_subword c (16,16):int16):int16)
         (word_sub (word 4:int16) (word_subword c (0,16):int16):int16):int32):int64)
       :int128) (64,64):int64) (16,16):int16):int32) 0)
      (word_shl (word_sx (word_subword (word_subword (word_join (word_join (word_join
         (word_sub (word 4:int16) (word_subword c (112,16):int16):int16)
         (word_sub (word 4:int16) (word_subword c (96,16):int16):int16):int32)
        (word_join (word_sub (word 4:int16) (word_subword c (80,16):int16):int16)
         (word_sub (word 4:int16) (word_subword c (64,16):int16):int16):int32):int64)
       (word_join (word_join
         (word_sub (word 4:int16) (word_subword c (48,16):int16):int16)
         (word_sub (word 4:int16) (word_subword c (32,16):int16):int16):int32)
        (word_join (word_sub (word 4:int16) (word_subword c (16,16):int16):int16)
         (word_sub (word 4:int16) (word_subword c (0,16):int16):int16):int32):int64)
       :int128) (64,64):int64) (0,16):int16):int32) 0):int64):int128
    ==>
    read (memory :> bytes (res, 16)) s =
    num_of_wordlist
      [word_sx(word_sub (word 4:int16) (word_subword c (64,16):int16)):int32;
       word_sx(word_sub (word 4:int16) (word_subword c (80,16):int16)):int32;
       word_sx(word_sub (word 4:int16) (word_subword c (96,16):int16)):int32;
       word_sx(word_sub (word 4:int16) (word_subword c (112,16):int16)):int32]`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC BYTES128_TO_WORDLIST THEN
  REWRITE_TAC[LENGTH] THEN CONJ_TAC THENL [ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[SSHLL_CHUNK_FROM_INT128_HI] THEN
  REWRITE_TAC[WORD_JOIN_4_INT32S_EQ_NUM_OF_WORDLIST]);;

(* BYTES8_INT16S_TO_BYTES64: the reverse direction of BYTES128_TO_WORDLIST_INT16  *)
(* at 64-bit width. Given bytes(a, 8) s = num_of_wordlist ws for a 4-int16 list,   *)
(* conclude bytes64 a s = word(num_of_wordlist ws). Used to relate b_k (from       *)
(* BIGNUM_LDIGITIZE) to int16 subsequences of STACK_CONTENT niblist. *)

let BYTES8_INT16S_TO_BYTES64 = prove
 (`!s:armstate (a:int64) (ws:int16 list).
    LENGTH ws = 4 /\
    read (memory :> bytes (a, 8)) s = num_of_wordlist ws
    ==>
    read (memory :> bytes64 a) s = word(num_of_wordlist ws)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `num_of_wordlist (ws:int16 list) < 2 EXP 64` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`ws:int16 list`; `64:num`] NUM_OF_WORDLIST_BOUND_GEN) THEN
    REWRITE_TAC[DIMINDEX_16] THEN ASM_REWRITE_TAC[] THEN ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[GSYM VAL_EQ; READ_COMPONENT_COMPOSE; BYTES64_WBYTES;
              VAL_READ_WBYTES; DIMINDEX_64; ARITH_RULE `64 DIV 8 = 8`;
              VAL_WORD; DIMINDEX_64] THEN
  REWRITE_TAC[GSYM READ_COMPONENT_COMPOSE] THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC SYM_CONV THEN
  MATCH_MP_TAC MOD_LT THEN ASM_REWRITE_TAC[]);;

(* SUB_LIST_SPLIT_AT: split a list at position i using SUB_LIST. *)

let SUB_LIST_SPLIT_AT = prove
 (`!(l:A list) i.
     i <= LENGTH l
     ==> l = APPEND (SUB_LIST(0, i) l) (SUB_LIST(i, LENGTH l - i) l)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`l:A list`; `i:num`] SUB_LIST_TOPSPLIT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> GEN_REWRITE_TAC LAND_CONV [SYM th]) THEN
  REFL_TAC);;

(* BK_FROM_STACK: main chunk-to-stack bridge. Given the stack invariant
   bytes(sp, 2*niblen) s = num_of_wordlist niblist and a chunk index k such
   that the k-th 8-byte chunk is within the niblist region (4*(k+1) <= niblen),
   the bytes64 read at sp+8*k equals word(num_of_wordlist [4 halfwords from
   niblist starting at index 4*k]). *)

let BK_FROM_STACK = prove
 (`!s:armstate. !sp:int64. !niblist:int16 list. !k:num.
    4 * (k + 1) <= LENGTH niblist /\
    read (memory :> bytes (sp, 2 * LENGTH niblist)) s = num_of_wordlist niblist
    ==>
    read (memory :> bytes64 (word_add sp (word (8 * k)))) s =
    word(num_of_wordlist (SUB_LIST(4*k, 4) niblist))`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC BYTES8_INT16S_TO_BYTES64 THEN
  REWRITE_TAC[LENGTH_SUB_LIST] THEN
  CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
    `read (memory :> bytes (sp, 2 * LENGTH(niblist:int16 list))) s =
     num_of_wordlist (APPEND (SUB_LIST(0, 4 * k) niblist)
                             (SUB_LIST(4 * k, LENGTH niblist - 4 * k) niblist))`
  MP_TAC THENL
   [MP_TAC(ISPECL [`niblist:int16 list`; `4 * k:num`] SUB_LIST_SPLIT_AT) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(fun th -> GEN_REWRITE_TAC
      (RAND_CONV o RAND_CONV o ONCE_DEPTH_CONV) [SYM th]) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `2 * LENGTH(niblist:int16 list) = 8 * k + (2 * LENGTH niblist - 8 * k)`
    (fun th -> GEN_REWRITE_TAC (LAND_CONV o LAND_CONV o ONCE_DEPTH_CONV) [th]) THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`memory:(armstate,(64)word->(8)word)component`;
                 `sp:int64`; `s:armstate`;
                 `SUB_LIST(0, 4 * k) (niblist:int16 list)`;
                 `SUB_LIST(4 * k, LENGTH(niblist:int16 list) - 4 * k) (niblist:int16 list)`;
                 `8 * k:num`; `2 * LENGTH(niblist:int16 list) - 8 * k:num`]
                BYTES_EQ_NUM_OF_WORDLIST_APPEND) THEN
  REWRITE_TAC[LENGTH_SUB_LIST; SUB_0; DIMINDEX_16] THEN
  SUBGOAL_THEN `MIN (4 * k) (LENGTH(niblist:int16 list)) = 4 * k` SUBST1_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  ANTS_TAC THENL [ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(fun th -> DISCH_THEN(MP_TAC o (REWRITE_RULE[th]))) THEN
  DISCH_THEN(MP_TAC o CONJUNCT2) THEN
  SUBGOAL_THEN
    `SUB_LIST(4 * k, LENGTH(niblist:int16 list) - 4 * k) niblist =
     APPEND (SUB_LIST(4 * k, 4) niblist)
            (SUB_LIST(4 * k + 4, LENGTH niblist - 4 * k - 4) niblist)`
  (fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV o ONCE_DEPTH_CONV) [th]) THENL
   [MP_TAC(ISPECL [`niblist:int16 list`; `4:num`; `LENGTH(niblist:int16 list) - 4 * k - 4`;
                   `4 * k:num`] SUB_LIST_SPLIT) THEN
    SUBGOAL_THEN `4 + LENGTH(niblist:int16 list) - 4 * k - 4 = LENGTH niblist - 4 * k`
      SUBST1_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN REFL_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `2 * LENGTH(niblist:int16 list) - 8 * k = 8 + (2 * LENGTH niblist - 8 * k - 8)`
    (fun th -> GEN_REWRITE_TAC (LAND_CONV o LAND_CONV o ONCE_DEPTH_CONV) [th]) THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`memory:(armstate,(64)word->(8)word)component`;
                 `word_add sp (word (8 * k)):int64`; `s:armstate`;
                 `SUB_LIST(4 * k, 4) (niblist:int16 list)`;
                 `SUB_LIST(4 * k + 4, LENGTH(niblist:int16 list) - 4 * k - 4) niblist`;
                 `8:num`; `2 * LENGTH(niblist:int16 list) - 8 * k - 8:num`]
                BYTES_EQ_NUM_OF_WORDLIST_APPEND) THEN
  REWRITE_TAC[LENGTH_SUB_LIST; DIMINDEX_16] THEN
  SUBGOAL_THEN `MIN 4 (LENGTH(niblist:int16 list) - 4 * k) = 4` SUBST1_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  ANTS_TAC THENL [ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(fun th -> DISCH_THEN(MP_TAC o (REWRITE_RULE[th]))) THEN
  DISCH_THEN(MP_TAC o CONJUNCT1) THEN
  REWRITE_TAC[]);;

(* BK_FROM_STACK_GE256: convenience wrapper for Case A. Requires k < 64 and
   256 <= LENGTH niblist (directly matching Case A hyps). *)

let BK_FROM_STACK_GE256 = prove
 (`!s:armstate. !sp:int64. !niblist:int16 list. !k:num.
    k < 64 /\ 256 <= LENGTH niblist /\
    read (memory :> bytes (sp, 2 * LENGTH niblist)) s = num_of_wordlist niblist
    ==>
    read (memory :> bytes64 (word_add sp (word (8 * k)))) s =
    word(num_of_wordlist (SUB_LIST(4*k, 4) niblist))`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC BK_FROM_STACK THEN ASM_REWRITE_TAC[] THEN
  ASM_ARITH_TAC);;

(* SSHLL_CHUNK_WORD_SUBWORD_LO_INT64 / _HI_INT64: BITBLAST-proven identities
   that collapse the (0,64) and (64,64) slices of one bytes128 SSHLL chunk
   to word_join of 2 int32 values. Used to simplify the 128 int64 LHS
   expressions that LEXPAND+SPLIT produces in Case A's writeback proof. *)

let SSHLL_CHUNK_WORD_SUBWORD_LO_INT64 = BITBLAST_RULE
 `word_subword
  (word_join
   (word_join
    (word_shl (word_sx (word_subword (word_subword
      (word_join (word_join (word_join
         (word_sub (word 4:int16) (word_subword (c:int128) (112,16):int16):int16)
         (word_sub (word 4:int16) (word_subword c (96,16):int16):int16):int32)
        (word_join (word_sub (word 4:int16) (word_subword c (80,16):int16):int16)
         (word_sub (word 4:int16) (word_subword c (64,16):int16):int16):int32):int64)
       (word_join (word_join
         (word_sub (word 4:int16) (word_subword c (48,16):int16):int16)
         (word_sub (word 4:int16) (word_subword c (32,16):int16):int16):int32)
        (word_join (word_sub (word 4:int16) (word_subword c (16,16):int16):int16)
         (word_sub (word 4:int16) (word_subword c (0,16):int16):int16):int32):int64)
       :int128) (0,64):int64) (48,16):int16):int32) 0)
    (word_shl (word_sx (word_subword (word_subword
      (word_join (word_join (word_join
         (word_sub (word 4:int16) (word_subword c (112,16):int16):int16)
         (word_sub (word 4:int16) (word_subword c (96,16):int16):int16):int32)
        (word_join (word_sub (word 4:int16) (word_subword c (80,16):int16):int16)
         (word_sub (word 4:int16) (word_subword c (64,16):int16):int16):int32):int64)
       (word_join (word_join
         (word_sub (word 4:int16) (word_subword c (48,16):int16):int16)
         (word_sub (word 4:int16) (word_subword c (32,16):int16):int16):int32)
        (word_join (word_sub (word 4:int16) (word_subword c (16,16):int16):int16)
         (word_sub (word 4:int16) (word_subword c (0,16):int16):int16):int32):int64)
       :int128) (0,64):int64) (32,16):int16):int32) 0):int64)
   (word_join
    (word_shl (word_sx (word_subword (word_subword
      (word_join (word_join (word_join
         (word_sub (word 4:int16) (word_subword c (112,16):int16):int16)
         (word_sub (word 4:int16) (word_subword c (96,16):int16):int16):int32)
        (word_join (word_sub (word 4:int16) (word_subword c (80,16):int16):int16)
         (word_sub (word 4:int16) (word_subword c (64,16):int16):int16):int32):int64)
       (word_join (word_join
         (word_sub (word 4:int16) (word_subword c (48,16):int16):int16)
         (word_sub (word 4:int16) (word_subword c (32,16):int16):int16):int32)
        (word_join (word_sub (word 4:int16) (word_subword c (16,16):int16):int16)
         (word_sub (word 4:int16) (word_subword c (0,16):int16):int16):int32):int64)
       :int128) (0,64):int64) (16,16):int16):int32) 0)
    (word_shl (word_sx (word_subword (word_subword
      (word_join (word_join (word_join
         (word_sub (word 4:int16) (word_subword c (112,16):int16):int16)
         (word_sub (word 4:int16) (word_subword c (96,16):int16):int16):int32)
        (word_join (word_sub (word 4:int16) (word_subword c (80,16):int16):int16)
         (word_sub (word 4:int16) (word_subword c (64,16):int16):int16):int32):int64)
       (word_join (word_join
         (word_sub (word 4:int16) (word_subword c (48,16):int16):int16)
         (word_sub (word 4:int16) (word_subword c (32,16):int16):int16):int32)
        (word_join (word_sub (word 4:int16) (word_subword c (16,16):int16):int16)
         (word_sub (word 4:int16) (word_subword c (0,16):int16):int16):int32):int64)
       :int128) (0,64):int64) (0,16):int16):int32) 0):int64):int128) (0,64):int64 =
  word_join (word_sx(word_sub (word 4:int16) (word_subword c (16,16):int16)):int32)
            (word_sx(word_sub (word 4:int16) (word_subword c (0,16):int16)):int32):int64`;;

let SSHLL_CHUNK_WORD_SUBWORD_HI_INT64 = BITBLAST_RULE
 `word_subword
  (word_join
   (word_join
    (word_shl (word_sx (word_subword (word_subword
      (word_join (word_join (word_join
         (word_sub (word 4:int16) (word_subword (c:int128) (112,16):int16):int16)
         (word_sub (word 4:int16) (word_subword c (96,16):int16):int16):int32)
        (word_join (word_sub (word 4:int16) (word_subword c (80,16):int16):int16)
         (word_sub (word 4:int16) (word_subword c (64,16):int16):int16):int32):int64)
       (word_join (word_join
         (word_sub (word 4:int16) (word_subword c (48,16):int16):int16)
         (word_sub (word 4:int16) (word_subword c (32,16):int16):int16):int32)
        (word_join (word_sub (word 4:int16) (word_subword c (16,16):int16):int16)
         (word_sub (word 4:int16) (word_subword c (0,16):int16):int16):int32):int64)
       :int128) (0,64):int64) (48,16):int16):int32) 0)
    (word_shl (word_sx (word_subword (word_subword
      (word_join (word_join (word_join
         (word_sub (word 4:int16) (word_subword c (112,16):int16):int16)
         (word_sub (word 4:int16) (word_subword c (96,16):int16):int16):int32)
        (word_join (word_sub (word 4:int16) (word_subword c (80,16):int16):int16)
         (word_sub (word 4:int16) (word_subword c (64,16):int16):int16):int32):int64)
       (word_join (word_join
         (word_sub (word 4:int16) (word_subword c (48,16):int16):int16)
         (word_sub (word 4:int16) (word_subword c (32,16):int16):int16):int32)
        (word_join (word_sub (word 4:int16) (word_subword c (16,16):int16):int16)
         (word_sub (word 4:int16) (word_subword c (0,16):int16):int16):int32):int64)
       :int128) (0,64):int64) (32,16):int16):int32) 0):int64)
   (word_join
    (word_shl (word_sx (word_subword (word_subword
      (word_join (word_join (word_join
         (word_sub (word 4:int16) (word_subword c (112,16):int16):int16)
         (word_sub (word 4:int16) (word_subword c (96,16):int16):int16):int32)
        (word_join (word_sub (word 4:int16) (word_subword c (80,16):int16):int16)
         (word_sub (word 4:int16) (word_subword c (64,16):int16):int16):int32):int64)
       (word_join (word_join
         (word_sub (word 4:int16) (word_subword c (48,16):int16):int16)
         (word_sub (word 4:int16) (word_subword c (32,16):int16):int16):int32)
        (word_join (word_sub (word 4:int16) (word_subword c (16,16):int16):int16)
         (word_sub (word 4:int16) (word_subword c (0,16):int16):int16):int32):int64)
       :int128) (0,64):int64) (16,16):int16):int32) 0)
    (word_shl (word_sx (word_subword (word_subword
      (word_join (word_join (word_join
         (word_sub (word 4:int16) (word_subword c (112,16):int16):int16)
         (word_sub (word 4:int16) (word_subword c (96,16):int16):int16):int32)
        (word_join (word_sub (word 4:int16) (word_subword c (80,16):int16):int16)
         (word_sub (word 4:int16) (word_subword c (64,16):int16):int16):int32):int64)
       (word_join (word_join
         (word_sub (word 4:int16) (word_subword c (48,16):int16):int16)
         (word_sub (word 4:int16) (word_subword c (32,16):int16):int16):int32)
        (word_join (word_sub (word 4:int16) (word_subword c (16,16):int16):int16)
         (word_sub (word 4:int16) (word_subword c (0,16):int16):int16):int32):int64)
       :int128) (0,64):int64) (0,16):int16):int32) 0):int64):int128) (64,64):int64 =
  word_join (word_sx(word_sub (word 4:int16) (word_subword c (48,16):int16)):int32)
            (word_sx(word_sub (word 4:int16) (word_subword c (32,16):int16)):int32):int64`;;

(* HI-INNER variants: when the chunk uses the (64,64) inner extraction
   (odd-indexed stack chunks, i.e., chunks at res+16j for j odd). *)

let SSHLL_CHUNK_WORD_SUBWORD_LO_INT64_HIINNER = BITBLAST_RULE
 `word_subword
  (word_join
   (word_join
    (word_shl (word_sx (word_subword (word_subword
      (word_join (word_join (word_join
         (word_sub (word 4:int16) (word_subword (c:int128) (112,16):int16):int16)
         (word_sub (word 4:int16) (word_subword c (96,16):int16):int16):int32)
        (word_join (word_sub (word 4:int16) (word_subword c (80,16):int16):int16)
         (word_sub (word 4:int16) (word_subword c (64,16):int16):int16):int32):int64)
       (word_join (word_join
         (word_sub (word 4:int16) (word_subword c (48,16):int16):int16)
         (word_sub (word 4:int16) (word_subword c (32,16):int16):int16):int32)
        (word_join (word_sub (word 4:int16) (word_subword c (16,16):int16):int16)
         (word_sub (word 4:int16) (word_subword c (0,16):int16):int16):int32):int64)
       :int128) (64,64):int64) (48,16):int16):int32) 0)
    (word_shl (word_sx (word_subword (word_subword
      (word_join (word_join (word_join
         (word_sub (word 4:int16) (word_subword c (112,16):int16):int16)
         (word_sub (word 4:int16) (word_subword c (96,16):int16):int16):int32)
        (word_join (word_sub (word 4:int16) (word_subword c (80,16):int16):int16)
         (word_sub (word 4:int16) (word_subword c (64,16):int16):int16):int32):int64)
       (word_join (word_join
         (word_sub (word 4:int16) (word_subword c (48,16):int16):int16)
         (word_sub (word 4:int16) (word_subword c (32,16):int16):int16):int32)
        (word_join (word_sub (word 4:int16) (word_subword c (16,16):int16):int16)
         (word_sub (word 4:int16) (word_subword c (0,16):int16):int16):int32):int64)
       :int128) (64,64):int64) (32,16):int16):int32) 0):int64)
   (word_join
    (word_shl (word_sx (word_subword (word_subword
      (word_join (word_join (word_join
         (word_sub (word 4:int16) (word_subword c (112,16):int16):int16)
         (word_sub (word 4:int16) (word_subword c (96,16):int16):int16):int32)
        (word_join (word_sub (word 4:int16) (word_subword c (80,16):int16):int16)
         (word_sub (word 4:int16) (word_subword c (64,16):int16):int16):int32):int64)
       (word_join (word_join
         (word_sub (word 4:int16) (word_subword c (48,16):int16):int16)
         (word_sub (word 4:int16) (word_subword c (32,16):int16):int16):int32)
        (word_join (word_sub (word 4:int16) (word_subword c (16,16):int16):int16)
         (word_sub (word 4:int16) (word_subword c (0,16):int16):int16):int32):int64)
       :int128) (64,64):int64) (16,16):int16):int32) 0)
    (word_shl (word_sx (word_subword (word_subword
      (word_join (word_join (word_join
         (word_sub (word 4:int16) (word_subword c (112,16):int16):int16)
         (word_sub (word 4:int16) (word_subword c (96,16):int16):int16):int32)
        (word_join (word_sub (word 4:int16) (word_subword c (80,16):int16):int16)
         (word_sub (word 4:int16) (word_subword c (64,16):int16):int16):int32):int64)
       (word_join (word_join
         (word_sub (word 4:int16) (word_subword c (48,16):int16):int16)
         (word_sub (word 4:int16) (word_subword c (32,16):int16):int16):int32)
        (word_join (word_sub (word 4:int16) (word_subword c (16,16):int16):int16)
         (word_sub (word 4:int16) (word_subword c (0,16):int16):int16):int32):int64)
       :int128) (64,64):int64) (0,16):int16):int32) 0):int64):int128) (0,64):int64 =
  word_join (word_sx(word_sub (word 4:int16) (word_subword c (80,16):int16)):int32)
            (word_sx(word_sub (word 4:int16) (word_subword c (64,16):int16)):int32):int64`;;

(* BIGNUM_OF_WORDLIST_EQ_NUM_OF_WORDLIST: bignum_of_wordlist is num_of_wordlist
   at int64 precision. *)

let BIGNUM_OF_WORDLIST_EQ_NUM_OF_WORDLIST = prove
 (`!l:int64 list. bignum_of_wordlist l = num_of_wordlist l`,
  LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[bignum_of_wordlist; num_of_wordlist; DIMINDEX_64]);;

(* BIGNUM_CONS_WORDJOIN: decompose one int64 = word_join of 2 int32s into
   num_of_wordlist of 2 int32s. *)

let BIGNUM_CONS_WORDJOIN = prove
 (`!a:int32. !b:int32. !t:int64 list.
     bignum_of_wordlist (CONS (word_join a b:int64) t) =
     num_of_wordlist [b; a] + 2 EXP 64 * bignum_of_wordlist t`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[bignum_of_wordlist; num_of_wordlist;
              DIMINDEX_32; MULT_CLAUSES; ADD_CLAUSES] THEN
  REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_JOIN; DIMINDEX_64; DIMINDEX_32] THEN
  MP_TAC(ISPEC `a:int32` VAL_BOUND) THEN
  MP_TAC(ISPEC `b:int32` VAL_BOUND) THEN
  REWRITE_TAC[DIMINDEX_32] THEN REPEAT DISCH_TAC THEN
  SUBGOAL_THEN `(2 EXP 32 * val(a:int32) + val(b:int32)) MOD 2 EXP 64 =
                2 EXP 32 * val a + val b` SUBST1_TAC THENL
   [MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC;
    ARITH_TAC]);;

(* VAL_WORD_JOIN_INT32_INT64: val(word_join a b:int64) = 2^32*val a + val b
   where a, b are int32. No MOD needed because the sum is already < 2^64.
   Used by BIGNUM_LIST_OF_SEQ_EQ_NUM_SUB_LIST below, so must come first. *)

let VAL_WORD_JOIN_INT32_INT64 = prove
 (`!a:int32. !b:int32.
     val (word_join (a:int32) (b:int32):int64) = 2 EXP 32 * val a + val b`,
  REPEAT GEN_TAC THEN REWRITE_TAC[VAL_WORD_JOIN; DIMINDEX_64; DIMINDEX_32] THEN
  MP_TAC(ISPEC `a:int32` VAL_BOUND) THEN
  MP_TAC(ISPEC `b:int32` VAL_BOUND) THEN
  REWRITE_TAC[DIMINDEX_32] THEN REPEAT DISCH_TAC THEN
  MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC);;

(* BIGNUM_LIST_OF_SEQ_EQ_NUM_SUB_LIST: full scaling lemma. For any n and any
   int16 list niblist with 2*n <= LENGTH niblist, the bignum_of_wordlist of
   the list_of_seq of int64 word_join pairs equals the num_of_wordlist of
   MAP f (SUB_LIST(0, 2*n) niblist), where f = \x. word_sx(word_sub (word 4) x).
   Proved by induction on n. *)

let BIGNUM_LIST_OF_SEQ_EQ_NUM_SUB_LIST = prove
 (`!niblist:int16 list. !n:num.
     2 * n <= LENGTH niblist
     ==>
     bignum_of_wordlist
       (list_of_seq (\i:num. word_join
           (word_sx (word_sub (word 4:int16) (EL (2*i+1) niblist)):int32)
           (word_sx (word_sub (word 4:int16) (EL (2*i) niblist)):int32):int64) n) =
     num_of_wordlist
       (MAP (\x. word_sx (word_sub (word 4:int16) x):int32)
            (SUB_LIST(0, 2*n) niblist))`,
  GEN_TAC THEN INDUCT_TAC THENL
   [REWRITE_TAC[MULT_CLAUSES; list_of_seq; bignum_of_wordlist;
                SUB_LIST_CLAUSES; MAP; num_of_wordlist];
    ALL_TAC] THEN
  DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_TAC] THEN
  REWRITE_TAC[list_of_seq;
              BIGNUM_OF_WORDLIST_APPEND; LENGTH_LIST_OF_SEQ;
              bignum_of_wordlist; MULT_CLAUSES; ADD_CLAUSES] THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[VAL_WORD_JOIN_INT32_INT64] THEN
  SUBGOAL_THEN
    `SUB_LIST(0, 2 + 2 * n) (niblist:int16 list) =
     APPEND (SUB_LIST(0, 2 * n) niblist) (SUB_LIST(2 * n, 2) niblist)`
    SUBST1_TAC THENL
   [MP_TAC(ISPECL [`niblist:int16 list`; `2*n:num`; `2`; `0`] SUB_LIST_SPLIT) THEN
    REWRITE_TAC[ADD_CLAUSES; ARITH_RULE `2 * n + 2 = 2 + 2 * n`] THEN
    DISCH_THEN SUBST1_TAC THEN REFL_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[MAP_APPEND; NUM_OF_WORDLIST_APPEND; DIMINDEX_32;
              LENGTH_MAP; LENGTH_SUB_LIST] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `MIN (2 * n) (LENGTH(niblist:int16 list) - 0) = 2 * n`
    SUBST1_TAC THENL
   [REWRITE_TAC[SUB_0] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  AP_TERM_TAC THEN
  REWRITE_TAC[ARITH_RULE `64 * n = 32 * 2 * n`] THEN
  AP_TERM_TAC THEN
  SUBGOAL_THEN `SUB_LIST(2 * n, 2) (niblist:int16 list) =
                [EL (2*n) niblist; EL (2*n+1) niblist]` SUBST1_TAC THENL
   [REWRITE_TAC[LIST_EQ; LENGTH_SUB_LIST; LENGTH] THEN
    CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    X_GEN_TAC `i:num` THEN REWRITE_TAC[ARITH_RULE `SUC(SUC 0) = 2`] THEN
    DISCH_TAC THEN
    MP_TAC(ISPECL [`niblist:int16 list`; `2*n:num`; `2`; `i:num`]
                  EL_SUB_LIST) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
    SUBGOAL_THEN `i = 0 \/ i = 1` MP_TAC THENL
     [ASM_ARITH_TAC;
      STRIP_TAC THEN ASM_REWRITE_TAC[EL; HD; TL; ADD_CLAUSES; num_CONV `1`]];
    REWRITE_TAC[MAP; num_of_wordlist; DIMINDEX_32; MULT_CLAUSES;
                ADD_CLAUSES] THEN ARITH_TAC]);;

Printf.printf "BIGNUM_LIST_OF_SEQ_EQ_NUM_SUB_LIST proved\n%!";;

(* SUB_LIST_EQ_LIST_OF_SEQ: SUB_LIST(0, n) l = list_of_seq (EL . l) n whenever
   n <= LENGTH l. Together with LIST_OF_SEQ_CONV this unfolds a prefix SUB_LIST
   to an explicit list. *)

let SUB_LIST_EQ_LIST_OF_SEQ = prove
 (`!n l:A list. n <= LENGTH l ==> SUB_LIST (0,n) l = list_of_seq (\i. EL i l) n`,
  INDUCT_TAC THENL
   [REWRITE_TAC[SUB_LIST_CLAUSES; LIST_OF_SEQ]; ALL_TAC] THEN
  LIST_INDUCT_TAC THENL [REWRITE_TAC[LENGTH] THEN ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[SUB_LIST_CLAUSES; LIST_OF_SEQ; LENGTH; LE_SUC] THEN
  DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `t:A list`) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[EL; HD; TL; o_THM] THEN
  AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[FUN_EQ_THM; o_THM; EL; TL]);;

(* PAIR_MAP_IDX_128: the Case A writeback identity. For any niblist of length
   at least 256, the bignum_of_wordlist of 128 explicit int64 word_joins
   (each packing two int32s of the form word_sx(word_sub (word 4) (EL k niblist)))
   equals num_of_wordlist of MAP (word_sx o word_sub(word 4)) over the 256-byte
   prefix SUB_LIST(0,256) niblist. Proof strategy: (1) BIGNUM_OF_WORDLIST_EQ_NUM_OF_WORDLIST,
   (2) collapse via GSYM pair_wordlist starting from the tail NIL, (3) NUM_OF_PAIR_WORDLIST
   to peel off pair_wordlist, (4) SUB_LIST_EQ_LIST_OF_SEQ + LIST_OF_SEQ_CONV to
   expand the SUB_LIST on RHS, (5) MAP clauses to match element-wise.
   The LHS list is an explicit 128-entry form — built below via LIST_OF_SEQ_CONV
   to avoid transcribing 128 entries manually. *)

let PAIR_MAP_IDX_128 =
  let pairs_str = String.concat ";\n      "
    (List.map (fun k ->
       Printf.sprintf
         "word_join (word_sx (word_sub (word 4:int16) (EL %d l)):int32) (word_sx (word_sub (word 4:int16) (EL %d l)):int32)"
         (2*k+1) (2*k)) (0--127)) in
  let goal_str = Printf.sprintf
    "!l:int16 list. 256 <= LENGTH l ==> \
     bignum_of_wordlist [%s] = \
     num_of_wordlist (MAP (\\x:int16. word_sx (word_sub (word 4) x):int32) (SUB_LIST (0,256) l))"
    pairs_str in
  prove
   (parse_term goal_str,
    REPEAT STRIP_TAC THEN
    REWRITE_TAC[BIGNUM_OF_WORDLIST_EQ_NUM_OF_WORDLIST] THEN
    SUBGOAL_THEN `[]:int64 list = pair_wordlist ([]:int32 list)` (fun th ->
      GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [th]) THENL
     [REWRITE_TAC[pair_wordlist]; ALL_TAC] THEN
    REWRITE_TAC[GSYM(el 0 (CONJUNCTS pair_wordlist))] THEN
    REWRITE_TAC[NUM_OF_PAIR_WORDLIST] THEN
    MP_TAC(ISPECL [`256`; `l:int16 list`] SUB_LIST_EQ_LIST_OF_SEQ) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN SUBST1_TAC THEN
    CONV_TAC(RAND_CONV(RAND_CONV(RAND_CONV LIST_OF_SEQ_CONV))) THEN
    REWRITE_TAC[MAP]);;

(* BIGNUM_WORDJOIN_PAIRS_EXISTS: for any even-length int32 list, there exists
   a unique int64-pair list whose bignum_of_wordlist equals num_of_wordlist l.
   Each pairs[i] = word_join (EL (2i+1) l) (EL (2i) l). *)

let BIGNUM_WORDJOIN_PAIRS_EXISTS = prove
 (`!n l:int32 list. LENGTH l = 2 * n
   ==> ?pairs:int64 list.
         LENGTH pairs = n /\
         bignum_of_wordlist pairs = num_of_wordlist l /\
         (!i. i < n ==> EL i pairs = word_join (EL (2*i+1) l) (EL (2*i) l))`,
  INDUCT_TAC THENL
   [REWRITE_TAC[MULT_CLAUSES; LENGTH_EQ_NIL] THEN
    GEN_TAC THEN DISCH_THEN SUBST1_TAC THEN
    EXISTS_TAC `[]:int64 list` THEN
    REWRITE_TAC[LENGTH; bignum_of_wordlist; num_of_wordlist; LT];
    ALL_TAC] THEN
  LIST_INDUCT_TAC THENL
   [REWRITE_TAC[LENGTH] THEN ARITH_TAC; ALL_TAC] THEN
  STRUCT_CASES_TAC (ISPEC `t:int32 list` list_CASES) THENL
   [REWRITE_TAC[LENGTH] THEN ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[LENGTH;
    ARITH_RULE `SUC(SUC(LENGTH(t':int32 list))) = 2 * SUC n <=>
                LENGTH t' = 2 * n`] THEN
  DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `t':int32 list`) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `pairs:int64 list` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `CONS (word_join (h':int32) (h:int32):int64) pairs` THEN
  ASM_REWRITE_TAC[LENGTH] THEN
  CONJ_TAC THENL
   [MP_TAC(SPECL [`h':int32`; `h:int32`; `pairs:int64 list`]
                 BIGNUM_CONS_WORDJOIN) THEN
    DISCH_THEN SUBST1_TAC THEN
    ASM_REWRITE_TAC[num_of_wordlist; DIMINDEX_32] THEN ARITH_TAC;
    X_GEN_TAC `i:num` THEN
    STRUCT_CASES_TAC (SPEC `i:num` num_CASES) THENL
     [REWRITE_TAC[EL; HD; MULT_CLAUSES; ADD_CLAUSES; TL] THEN
      REWRITE_TAC[ARITH_RULE `1 = SUC 0`; EL; TL; HD];
      REWRITE_TAC[EL; TL; LT_SUC] THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `n':num`) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
      REWRITE_TAC[ARITH_RULE `2 * SUC n' + 1 = SUC(SUC(2 * n' + 1)) /\
                               2 * SUC n' = SUC(SUC(2 * n'))`] THEN
      REWRITE_TAC[EL; TL; HD]]]);;

(* BIGNUM_WORDJOIN_APPEND: inductive step — given tail equals num_of_wordlist form,
   CONS of word_join equals APPEND of 2-element prefix. *)

let BIGNUM_WORDJOIN_APPEND = prove
 (`!a:int32. !b:int32. !t:int64 list. !tlist:int32 list.
     bignum_of_wordlist t = num_of_wordlist tlist /\
     32 * LENGTH tlist = 64 * LENGTH t
     ==>
     bignum_of_wordlist (CONS (word_join a b:int64) t) =
     num_of_wordlist (APPEND [b; a] tlist)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[NUM_OF_WORDLIST_APPEND; DIMINDEX_32] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(SPECL [`a:int32`; `b:int32`; `t:int64 list`] BIGNUM_CONS_WORDJOIN) THEN
  DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[num_of_wordlist; DIMINDEX_32; LENGTH; MULT_CLAUSES; ADD_CLAUSES] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[ARITH_RULE `2 EXP 64 = 2 EXP 64`] THEN
  ARITH_TAC);;

let SSHLL_CHUNK_WORD_SUBWORD_HI_INT64_HIINNER = BITBLAST_RULE
 `word_subword
  (word_join
   (word_join
    (word_shl (word_sx (word_subword (word_subword
      (word_join (word_join (word_join
         (word_sub (word 4:int16) (word_subword (c:int128) (112,16):int16):int16)
         (word_sub (word 4:int16) (word_subword c (96,16):int16):int16):int32)
        (word_join (word_sub (word 4:int16) (word_subword c (80,16):int16):int16)
         (word_sub (word 4:int16) (word_subword c (64,16):int16):int16):int32):int64)
       (word_join (word_join
         (word_sub (word 4:int16) (word_subword c (48,16):int16):int16)
         (word_sub (word 4:int16) (word_subword c (32,16):int16):int16):int32)
        (word_join (word_sub (word 4:int16) (word_subword c (16,16):int16):int16)
         (word_sub (word 4:int16) (word_subword c (0,16):int16):int16):int32):int64)
       :int128) (64,64):int64) (48,16):int16):int32) 0)
    (word_shl (word_sx (word_subword (word_subword
      (word_join (word_join (word_join
         (word_sub (word 4:int16) (word_subword c (112,16):int16):int16)
         (word_sub (word 4:int16) (word_subword c (96,16):int16):int16):int32)
        (word_join (word_sub (word 4:int16) (word_subword c (80,16):int16):int16)
         (word_sub (word 4:int16) (word_subword c (64,16):int16):int16):int32):int64)
       (word_join (word_join
         (word_sub (word 4:int16) (word_subword c (48,16):int16):int16)
         (word_sub (word 4:int16) (word_subword c (32,16):int16):int16):int32)
        (word_join (word_sub (word 4:int16) (word_subword c (16,16):int16):int16)
         (word_sub (word 4:int16) (word_subword c (0,16):int16):int16):int32):int64)
       :int128) (64,64):int64) (32,16):int16):int32) 0):int64)
   (word_join
    (word_shl (word_sx (word_subword (word_subword
      (word_join (word_join (word_join
         (word_sub (word 4:int16) (word_subword c (112,16):int16):int16)
         (word_sub (word 4:int16) (word_subword c (96,16):int16):int16):int32)
        (word_join (word_sub (word 4:int16) (word_subword c (80,16):int16):int16)
         (word_sub (word 4:int16) (word_subword c (64,16):int16):int16):int32):int64)
       (word_join (word_join
         (word_sub (word 4:int16) (word_subword c (48,16):int16):int16)
         (word_sub (word 4:int16) (word_subword c (32,16):int16):int16):int32)
        (word_join (word_sub (word 4:int16) (word_subword c (16,16):int16):int16)
         (word_sub (word 4:int16) (word_subword c (0,16):int16):int16):int32):int64)
       :int128) (64,64):int64) (16,16):int16):int32) 0)
    (word_shl (word_sx (word_subword (word_subword
      (word_join (word_join (word_join
         (word_sub (word 4:int16) (word_subword c (112,16):int16):int16)
         (word_sub (word 4:int16) (word_subword c (96,16):int16):int16):int32)
        (word_join (word_sub (word 4:int16) (word_subword c (80,16):int16):int16)
         (word_sub (word 4:int16) (word_subword c (64,16):int16):int16):int32):int64)
       (word_join (word_join
         (word_sub (word 4:int16) (word_subword c (48,16):int16):int16)
         (word_sub (word 4:int16) (word_subword c (32,16):int16):int16):int32)
        (word_join (word_sub (word 4:int16) (word_subword c (16,16):int16):int16)
         (word_sub (word 4:int16) (word_subword c (0,16):int16):int16):int32):int64)
       :int128) (64,64):int64) (0,16):int16):int32) 0):int64):int128) (64,64):int64 =
  word_join (word_sx(word_sub (word 4:int16) (word_subword c (112,16):int16)):int32)
            (word_sx(word_sub (word 4:int16) (word_subword c (96,16):int16)):int32):int64`;;

(* STACK_CONTENT_FROM_PARTS: combine live niblist on stack (bytes(sp, 2*LENGTH n))  *)
(* with zero-tail (bytes(sp+2*LENGTH n, 512-2*LENGTH n) = 0) into a single          *)
(* 512-byte stack statement as num_of_wordlist (STACK_CONTENT newlist).             *)

let STACK_CONTENT_FROM_PARTS = prove
 (`!s:armstate sp:int64 (newlist:int16 list).
    LENGTH newlist <= 256 /\
    read (memory :> bytes (sp, 2 * LENGTH newlist)) s =
    num_of_wordlist newlist /\
    read (memory :> bytes (word_add sp (word (2 * LENGTH newlist)),
                           512 - 2 * LENGTH newlist)) s = 0
    ==>
    read (memory :> bytes (sp, 512)) s =
    num_of_wordlist (STACK_CONTENT newlist)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `newlist:int16 list` STACK_CONTENT_SMALL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`memory:(armstate,(64)word->(8)word)component`;
                 `s:armstate`; `sp:int64`;
                 `newlist:int16 list`;
                 `2 * LENGTH(newlist:int16 list)`;
                 `512 - 2 * LENGTH(newlist:int16 list)`;
                 `256 - LENGTH(newlist:int16 list)`] BYTES_APPEND_ZEROS) THEN
  REWRITE_TAC[DIMINDEX_16] THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `2 * LENGTH(newlist:int16 list) + 512 - 2 * LENGTH newlist = 512`
    SUBST1_TAC THENL
   [ASM_ARITH_TAC; DISCH_THEN ACCEPT_TAC]);;

let REJ_SAMPLE_ETA4_SUB_LIST_PREFIX = prove
 (`!k (l:byte list).
     k <= LENGTH l
     ==> ?rest:int32 list.
         APPEND (REJ_SAMPLE_ETA4 (SUB_LIST (0,k) l)) rest =
         REJ_SAMPLE_ETA4 l`,
  REPEAT STRIP_TAC THEN
  EXISTS_TAC `REJ_SAMPLE_ETA4 (SUB_LIST(k, LENGTH l - k) l):int32 list` THEN
  REWRITE_TAC[REJ_SAMPLE_ETA4; GSYM MAP_APPEND] THEN
  AP_TERM_TAC THEN
  REWRITE_TAC[REJ_NIBBLES_ETA4; GSYM FILTER_APPEND] THEN
  AP_TERM_TAC THEN
  REWRITE_TAC[GSYM NIBBLES_OF_BYTES_APPEND] THEN
  AP_TERM_TAC THEN
  MP_TAC(ISPECL [`l:byte list`; `k:num`] SUB_LIST_TOPSPLIT) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(fun th -> GEN_REWRITE_TAC RAND_CONV [SYM th]) THEN
  REFL_TAC);;

let REJ_NIBBLES_ETA4_SPLIT_8 = prove
 (`!b0 b1 b2 b3 b4 b5 b6 b7:byte.
     REJ_NIBBLES_ETA4 [b0;b1;b2;b3;b4;b5;b6;b7] =
     APPEND (REJ_NIBBLES_ETA4 [b0;b1;b2;b3])
            (REJ_NIBBLES_ETA4 [b4;b5;b6;b7]:int16 list)`,
  REPEAT GEN_TAC THEN
  SUBST1_TAC(SYM(EQT_ELIM(REWRITE_CONV[APPEND]
    `APPEND [b0:byte;b1;b2;b3] [b4;b5;b6;b7] =
     [b0;b1;b2;b3;b4;b5;b6;b7]`))) THEN
  REWRITE_TAC[REJ_NIBBLES_ETA4_APPEND]);;

(* CASE_B_TRUNCATE: given the FULL 1024-byte memory identity
     read bytes(res, 1024) s = num_of_wordlist(MAP f (STACK_CONTENT niblist))
   and niblen <= 256, derive the truncated identity
     read bytes(res, 4*niblen) s = num_of_wordlist(MAP f niblist).
   Proof: take MOD 2^(8*4*niblen) of both sides.
   LHS: read bytes(res, 1024) s MOD 2^(8*4*niblen) = read bytes(res, MIN 1024 (4*niblen)) s
        = read bytes(res, 4*niblen) s (since 4*niblen <= 1024).
   RHS: num_of_wordlist L :int32 MOD 2^(32*niblen) = num_of_wordlist(SUB_LIST(0,niblen) L).
   Then SUB_LIST(0, niblen)(MAP f (STACK_CONTENT niblist)) = MAP f niblist via
   SUB_LIST_MAP + SUB_LIST_MIN + SUB_LIST_APPEND_LEFT + SUB_LIST_REFL. *)

let CASE_B_TRUNCATE = prove
 (`!res:int64 niblen:num niblist:int16 list s:armstate.
    niblen <= 256 /\
    LENGTH niblist = niblen /\
    read (memory :> bytes (res, 1024)) s =
    num_of_wordlist (MAP (\x:int16. word_sx(word_sub (word 4:int16) x):int32)
                         (STACK_CONTENT niblist))
    ==>
    read (memory :> bytes (res, 4 * niblen)) s =
    num_of_wordlist (MAP (\x:int16. word_sx(word_sub (word 4:int16) x):int32) niblist)`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o AP_TERM `(\n:num. n MOD 2 EXP (8 * (4 * niblen)))`) THEN
  CONV_TAC(ONCE_DEPTH_CONV BETA_CONV) THEN
  REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_MOD] THEN
  SUBGOAL_THEN `MIN 1024 (4 * niblen) = 4 * niblen` SUBST1_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `8 * 4 * niblen = dimindex(:32) * niblen` SUBST1_TAC THENL
   [REWRITE_TAC[DIMINDEX_32] THEN ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[GSYM NUM_OF_WORDLIST_SUB_LIST_0] THEN
  SUBGOAL_THEN
    `SUB_LIST(0, niblen)
       (MAP (\x:int16. word_sx(word_sub (word 4:int16) x):int32) (STACK_CONTENT niblist)) =
     MAP (\x:int16. word_sx(word_sub (word 4:int16) x):int32) niblist`
    SUBST1_TAC THENL
   [REWRITE_TAC[GSYM SUB_LIST_MAP; STACK_CONTENT; SUB_LIST_MIN] THEN
    SUBGOAL_THEN `MIN niblen 256 = niblen` SUBST1_TAC THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[MAP_APPEND] THEN
    MP_TAC(ISPECL [`MAP (\x:int16. word_sx(word_sub (word 4:int16) x):int32) niblist`;
                   `MAP (\x:int16. word_sx(word_sub (word 4:int16) x):int32)
                        (REPLICATE 256 (word 0:int16))`;
                   `niblen:num`] SUB_LIST_APPEND_LEFT) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[LENGTH_MAP] THEN ASM_REWRITE_TAC[LE_REFL]; ALL_TAC] THEN
    DISCH_THEN SUBST1_TAC THEN
    MATCH_MP_TAC SUB_LIST_REFL THEN
    REWRITE_TAC[LENGTH_MAP] THEN ASM_REWRITE_TAC[LE_REFL];
    REWRITE_TAC[]]);;

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

let PRINT_GOAL_TAC = fun g ->
  let (_, goal) = g in
  Printf.printf "==== GOAL ====\n%s\n==============\n%!" (string_of_term goal);
  ALL_TAC g;;

let DUMP_STATE_TAC path = fun g ->
  let (hyps, goal) = g in
  let oc = open_out path in
  output_string oc (Printf.sprintf "=== GOAL ===\n%s\n\n=== HYPS (%d) ===\n"
    (string_of_term goal) (List.length hyps));
  List.iter (fun (name, th) ->
    output_string oc (Printf.sprintf "[%s]: %s\n\n" name
      (string_of_term (concl th)))) hyps;
  close_out oc;
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
   DISCH_THEN(fun th ->
     MAP_EVERY ASSUME_TAC (CONJUNCTS th)) THEN
   DBG "04f after DISCH chain" THEN
   DUMP_STATE_TAC "/tmp/eta4/cheat1_after_disch.txt" THEN
   SUBGOAL_THEN `val(word niblen:int64) = niblen` ASSUME_TAC THENL
    [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN
     UNDISCH_TAC `niblen < 272` THEN ARITH_TAC; ALL_TAC] THEN
   DBG "04f1 after val(word niblen)" THEN
   (* Digitize the stackpointer memory into 64 8-byte abbrevs (b_0..b_63 =
      512 bytes) so that ARM_STEPS can step through the LDR Q16 reads. *)
   BIGNUM_LDIGITIZE_TAC "b_"
     `read (memory :> bytes(stackpointer,8 * 64)) s0` THEN
   DBG "04f2 after LDIGITIZE" THEN
   MEMORY_128_FROM_64_TAC "stackpointer" 0 32 THEN
   DBG "04f3 after MEMORY_128_FROM_64" THEN
   ASM_REWRITE_TAC[WORD_ADD_0] THEN STRIP_TAC THEN
   DBG "04f4 after ASM_REWRITE+STRIP" THEN
   (* Unroll the full writeback: preamble (4) + loop (15 * 16 = 240) + post (1 MOV X0).
      The final RET is implicit (PC at pc+336). *)
   ARM_STEPS_TAC MLDSA_REJ_UNIFORM_ETA4_EXEC (1--245) THEN
   DBG "04g after ARM 1-245 (full writeback)" THEN
   ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
   DBG "04h after ENSURES_FINAL" THEN
   (* Bridge between post-WOP invariant and final output:
      - niblist is a PREFIX of REJ_NIBBLES_ETA4 inlist;
        equivalently, REJ_SAMPLE_ETA4(SUB_LIST(0,8*nn) inlist) is a prefix
        of REJ_SAMPLE_ETA4 inlist.
      - Then LENGTH(SUB_LIST(0,256)(REJ_SAMPLE_ETA4 inlist)) = MIN 256 niblen.
      Case analysis on (buflen < 8*(nn+1) \/ 256 <= niblen):
        * niblen >= 256: first 256 of REJ_SAMPLE_ETA4 all come from niblist's
          prefix-image → LENGTH = 256 = X0.
        * buflen < 8*(nn+1) with 8 | buflen: then 8*nn = buflen, so
          SUB_LIST(0,8*nn) inlist = inlist, niblist = REJ_NIBBLES_ETA4 inlist,
          niblen = LENGTH(REJ_SAMPLE_ETA4 inlist), and MIN 256 niblen = niblen.
          X0 = word niblen = word(MIN 256 niblen). *)
   SUBGOAL_THEN
     `LENGTH(SUB_LIST(0,256)(REJ_SAMPLE_ETA4 inlist):int32 list) =
      MIN 256 niblen`
   ASSUME_TAC THENL
    [REWRITE_TAC[LENGTH_SUB_LIST; SUB_0] THEN
     FIRST_X_ASSUM DISJ_CASES_TAC THENL
      [(* Case A: buflen < 8*(nn+1). Together with 8 divides buflen,
          forces either 8*nn = buflen (SUB_LIST = inlist) or 8*nn > buflen
          (also SUB_LIST = inlist). Either way niblist = REJ_NIBBLES_ETA4 inlist. *)
       SUBGOAL_THEN `SUB_LIST(0, 8 * nn) (inlist:byte list) = inlist`
         SUBST_ALL_TAC THENL
        [MATCH_MP_TAC SUB_LIST_REFL THEN
         UNDISCH_TAC `8 divides buflen` THEN REWRITE_TAC[divides] THEN
         DISCH_THEN(X_CHOOSE_THEN `k:num` SUBST_ALL_TAC) THEN
         UNDISCH_TAC `LENGTH(inlist:byte list) = 8 * k` THEN
         DISCH_THEN SUBST1_TAC THEN
         REWRITE_TAC[LE_MULT_LCANCEL] THEN
         UNDISCH_TAC `8 * k < 8 * (nn + 1)` THEN
         REWRITE_TAC[LT_MULT_LCANCEL] THEN ARITH_TAC;
         ALL_TAC] THEN
       SUBGOAL_THEN `LENGTH(REJ_SAMPLE_ETA4 inlist:int32 list) = niblen`
         SUBST1_TAC THENL
        [REWRITE_TAC[REJ_SAMPLE_ETA4; LENGTH_MAP] THEN ASM_REWRITE_TAC[];
         REFL_TAC];
       (* Case B: 256 <= niblen. Split on 8*nn <= buflen? *)
       ASM_CASES_TAC `8 * nn <= LENGTH(inlist:byte list)` THENL
        [(* 8*nn <= buflen: prefix lemma gives APPEND niblist rest = REJ_SAMPLE *)
         MP_TAC(ISPECL [`8 * nn`; `inlist:byte list`]
                REJ_SAMPLE_ETA4_SUB_LIST_PREFIX) THEN
         ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
         DISCH_THEN(X_CHOOSE_THEN `rest:int32 list` ASSUME_TAC) THEN
         SUBGOAL_THEN
           `LENGTH(REJ_SAMPLE_ETA4 inlist:int32 list) =
            niblen + LENGTH(rest:int32 list)`
          SUBST1_TAC THENL
          [FIRST_X_ASSUM(fun th ->
             GEN_REWRITE_TAC(LAND_CONV o ONCE_DEPTH_CONV)[SYM th]) THEN
           REWRITE_TAC[LENGTH_APPEND; REJ_SAMPLE_ETA4; LENGTH_MAP] THEN
           ASM_REWRITE_TAC[];
           ALL_TAC] THEN
         UNDISCH_TAC `256 <= niblen` THEN ARITH_TAC;
         (* 8*nn > buflen: SUB_LIST clips *)
         SUBGOAL_THEN `SUB_LIST(0, 8 * nn) (inlist:byte list) = inlist`
           SUBST_ALL_TAC THENL
          [MATCH_MP_TAC SUB_LIST_REFL THEN ASM_ARITH_TAC;
           ALL_TAC] THEN
         SUBGOAL_THEN `LENGTH(REJ_SAMPLE_ETA4 inlist:int32 list) = niblen`
           SUBST1_TAC THENL
          [REWRITE_TAC[REJ_SAMPLE_ETA4; LENGTH_MAP] THEN ASM_REWRITE_TAC[];
           REFL_TAC]]]; ALL_TAC] THEN
   DBG "04i after length equation" THEN
   ASM_REWRITE_TAC[] THEN
   DBG "04j after ASM_REWRITE length equation" THEN
   CONJ_TAC THENL
    [(* Conjunct 1: word(MIN 256 niblen) = if niblen < 256 then word niblen else word 256 *)
     COND_CASES_TAC THEN AP_TERM_TAC THEN ASM_ARITH_TAC;
     (* Conjunct 2: read memory s245 = num_of_wordlist SUB_LIST. *)
     DUMP_STATE_TAC "/tmp/eta4/cheat1_state.txt" THEN
     (* Stage 1: split on WOP disjunction — 1 CHEAT becomes 2, enabling
        independent work on each case. *)
     FIRST_X_ASSUM(DISJ_CASES_THEN ASSUME_TAC) THENL
      [(* Case B: buflen < 8*(nn+1). SUB_LIST(0, 8*nn) inlist = inlist,
          so niblist = REJ_NIBBLES_ETA4 inlist. *)
       DBG "04k CASE_B buflen<..." THEN
       SUBGOAL_THEN `SUB_LIST(0, 8 * nn) (inlist:byte list) = inlist`
         ASSUME_TAC THENL
        [MATCH_MP_TAC SUB_LIST_8nn_INLIST THEN EXISTS_TAC `buflen:num` THEN
         ASM_REWRITE_TAC[];
         ALL_TAC] THEN
       (* REJ_SAMPLE_ETA4 inlist = MAP f niblist (since SUB_LIST(0,8*nn)=inlist). *)
       SUBGOAL_THEN
        `REJ_SAMPLE_ETA4 (inlist:byte list) =
         MAP (\x. word_sx(word_sub (word 4:int16) x):int32) niblist`
       ASSUME_TAC THENL
        [REWRITE_TAC[REJ_SAMPLE_ETA4] THEN AP_TERM_TAC THEN
         UNDISCH_TAC
           `REJ_NIBBLES_ETA4 (SUB_LIST(0,8 * nn) (inlist:byte list)) =
            (niblist:int16 list)` THEN
         ASM_REWRITE_TAC[];
         ALL_TAC] THEN
       DBG "04k1 CASE_B after REJ_SAMPLE=MAP" THEN
       (* Sub-case split: niblen >= 256 reuses Case A path; niblen < 256 is  *)
       (* the "true" Case B needing STACK_CONTENT_SMALL + prefix extraction.  *)
       ASM_CASES_TAC `256 <= niblen` THENL
        [(* niblen >= 256 sub-branch: reuses Case A closure verbatim.        *)
         DBG "04k2_large CASE_B (niblen >= 256 — Case A path)" THEN
         SUBGOAL_THEN `MIN 256 niblen = 256` SUBST1_TAC THENL
          [ASM_ARITH_TAC; ALL_TAC] THEN
         REWRITE_TAC[ARITH_RULE `4 * 256 = 1024`] THEN
         SUBGOAL_THEN
          `SUB_LIST(0,256)(REJ_SAMPLE_ETA4 (inlist:byte list)) =
           SUB_LIST(0,256)(MAP (\x. word_sx(word_sub (word 4:int16) x):int32)
                             (niblist:int16 list))`
         SUBST1_TAC THENL
          [ASM_REWRITE_TAC[];
           ALL_TAC] THEN
         REWRITE_TAC[SUB_LIST_MAP] THEN
         SUBGOAL_THEN
           `SUB_LIST(0, 256) (niblist:int16 list) = STACK_CONTENT niblist`
         SUBST1_TAC THENL
          [CONV_TAC SYM_CONV THEN MATCH_MP_TAC STACK_CONTENT_LARGE THEN
           UNDISCH_TAC `LENGTH(niblist:int16 list) = niblen` THEN
           DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[];
           ALL_TAC] THEN
         MP_TAC(GEN `k:num` (ISPECL [`s245:armstate`; `stackpointer:int64`;
                                      `niblist:int16 list`; `k:num`]
                                     BK_FROM_STACK_GE256)) THEN
         ASM_REWRITE_TAC[] THEN
         DISCH_THEN(fun bk_univ ->
           MAP_EVERY (fun i ->
             let inst = SPEC (mk_small_numeral i) bk_univ in
             let premise = EQT_ELIM (NUM_LT_CONV (lhand(concl inst))) in
             ASSUME_TAC (MP inst premise)) (0--63)) THEN
         RULE_ASSUM_TAC(CONV_RULE(DEPTH_CONV NUM_MULT_CONV)) THEN
         RULE_ASSUM_TAC(REWRITE_RULE[WORD_ADD_0]) THEN
         (fun (asl, _ as gl) ->
           let bk_trans_thms = List.filter_map (fun (_, th) ->
             let c = concl th in
             if is_eq c then
               let rhs = rand c in
               if is_var rhs && String.length (fst (dest_var rhs)) >= 2 &&
                  String.sub (fst (dest_var rhs)) 0 2 = "b_" then
                 let lhs = lhand c in
                 let bk_fact = List.find_opt (fun (_, th2) ->
                   let c2 = concl th2 in
                   is_eq c2 && lhs = lhand c2 && rhs <> rand c2) asl in
                 (match bk_fact with
                  | Some (_, bk_th) -> Some (TRANS (SYM th) bk_th)
                  | None -> None)
               else None
             else None) asl in
           MAP_EVERY ASSUME_TAC bk_trans_thms gl) THEN
         REWRITE_TAC[ARITH_RULE `1024 = 8 * 128`] THEN
         CONV_TAC(ONCE_DEPTH_CONV BIGNUM_LEXPAND_CONV) THEN
         RULE_ASSUM_TAC(CONV_RULE(ONCE_DEPTH_CONV(READ_MEMORY_SPLIT_CONV 1))) THEN
         ASM_REWRITE_TAC[] THEN
         REWRITE_TAC[SSHLL_CHUNK_WORD_SUBWORD_LO_INT64;
                     SSHLL_CHUNK_WORD_SUBWORD_HI_INT64;
                     SSHLL_CHUNK_WORD_SUBWORD_LO_INT64_HIINNER;
                     SSHLL_CHUNK_WORD_SUBWORD_HI_INT64_HIINNER] THEN
         SUBGOAL_THEN `256 <= LENGTH (niblist:int16 list)` ASSUME_TAC THENL
          [UNDISCH_TAC `LENGTH(niblist:int16 list) = niblen` THEN
           DISCH_THEN SUBST1_TAC THEN
           UNDISCH_TAC `256 <= niblen` THEN REWRITE_TAC[];
           ALL_TAC] THEN
         MP_TAC(GEN `a:num` (ISPECL [`niblist:int16 list`; `a:num`]
                                    WORD_SUBWORD_JOIN_SUB_LIST_H)) THEN
         DISCH_THEN(fun univ_th ->
           MAP_EVERY (fun i ->
             let inst = SPEC (mk_small_numeral i) univ_th in
             let prem_term = lhand(concl inst) in
             let prem_thm = ARITH_RULE(mk_imp(
               `256 <= LENGTH (niblist:int16 list)`, prem_term)) in
             let raw = MATCH_MP inst
               (MP prem_thm (ASSUME `256 <= LENGTH (niblist:int16 list)`)) in
             let discharged = CONV_RULE (REWRITE_CONV[ARITH]) raw in
             REWRITE_TAC[discharged])
             (List.map (fun k -> 8 * k) (0--31))) THEN
         SUBGOAL_THEN `STACK_CONTENT (niblist:int16 list) = SUB_LIST(0, 256) niblist`
           SUBST1_TAC THENL
          [MATCH_MP_TAC STACK_CONTENT_LARGE THEN ASM_REWRITE_TAC[];
           ALL_TAC] THEN
         MP_TAC(ISPECL
           [`128`;
            `MAP (\x. word_sx (word_sub (word 4:int16) x):int32)
                 (SUB_LIST(0, 256) (niblist:int16 list))`]
           BIGNUM_WORDJOIN_PAIRS_EXISTS) THEN
         ANTS_TAC THENL
          [REWRITE_TAC[LENGTH_MAP; LENGTH_SUB_LIST] THEN
           UNDISCH_TAC `256 <= LENGTH (niblist:int16 list)` THEN ARITH_TAC;
           ALL_TAC] THEN
         DISCH_THEN(X_CHOOSE_THEN `pairs:int64 list` STRIP_ASSUME_TAC) THEN
         MP_TAC(ISPECL [`niblist:int16 list`; `128`]
                       BIGNUM_LIST_OF_SEQ_EQ_NUM_SUB_LIST) THEN
         ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
         REWRITE_TAC[ARITH_RULE `2 * 128 = 256`] THEN
         DISCH_THEN(SUBST1_TAC o SYM) THEN
         AP_TERM_TAC THEN
         CONV_TAC SYM_CONV THEN
         CONV_TAC(LAND_CONV (
           REWRITE_CONV (list_of_seq :: APPEND ::
             List.map (fun k -> num_CONV (mk_small_numeral k)) (1--128))
           THENC TOP_DEPTH_CONV BETA_CONV
           THENC NUM_REDUCE_CONV)) THEN
         REFL_TAC;
         (* True Case B sub-branch: niblen < 256 *)
         DBG "04k2_small CASE_B (niblen < 256)" THEN
         SUBGOAL_THEN `niblen < 256` ASSUME_TAC THENL
          [ASM_ARITH_TAC; ALL_TAC] THEN
         SUBGOAL_THEN `MIN 256 niblen = niblen` SUBST1_TAC THENL
          [ASM_ARITH_TAC; ALL_TAC] THEN
         SUBGOAL_THEN
           `SUB_LIST(0,256)(REJ_SAMPLE_ETA4 (inlist:byte list)) =
            MAP (\x. word_sx(word_sub (word 4:int16) x):int32) niblist`
           SUBST1_TAC THENL
          [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SUB_LIST_REFL THEN
           REWRITE_TAC[LENGTH_MAP] THEN ASM_ARITH_TAC;
           ALL_TAC] THEN
         DBG "04l CASE_B_small after simplifications" THEN
         DUMP_STATE_TAC "/tmp/eta4/case_b_small.txt" THEN
         CHEAT_TAC];
       (* Case A: 256 <= niblen. Simplify MIN to 256, then rewrite RHS via
          prefix lemma to SUB_LIST(0,256)(MAP f niblist). *)
       DBG "04k CASE_A 256<=niblen" THEN
       SUBGOAL_THEN `MIN 256 niblen = 256` SUBST1_TAC THENL
        [ASM_ARITH_TAC; ALL_TAC] THEN
       REWRITE_TAC[ARITH_RULE `4 * 256 = 1024`] THEN
       (* Prefix bridge: SUB_LIST(0,256)(REJ_SAMPLE_ETA4 inlist) =
          SUB_LIST(0,256)(MAP f niblist). *)
       SUBGOAL_THEN
        `SUB_LIST(0,256)(REJ_SAMPLE_ETA4 (inlist:byte list)) =
         SUB_LIST(0,256)(MAP (\x. word_sx(word_sub (word 4:int16) x):int32)
                           (niblist:int16 list))`
       SUBST1_TAC THENL
        [MP_TAC(SPECL [`inlist:byte list`; `nn:num`] SUB_LIST_256_PREFIX_LARGE) THEN
         ANTS_TAC THENL
          [(* 256 <= LENGTH(REJ_NIBBLES_ETA4(SUB_LIST(0, 8*nn) inlist)) *)
           UNDISCH_TAC
             `REJ_NIBBLES_ETA4 (SUB_LIST(0,8 * nn) (inlist:byte list)) =
              (niblist:int16 list)` THEN
           DISCH_THEN SUBST1_TAC THEN
           UNDISCH_TAC `LENGTH(niblist:int16 list) = niblen` THEN
           DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[];
           ALL_TAC] THEN
         DISCH_THEN SUBST1_TAC THEN AP_TERM_TAC THEN
         ASM_REWRITE_TAC[REJ_SAMPLE_ETA4];
         ALL_TAC] THEN
       DBG "04l CASE_A after prefix bridge" THEN
       (* SUB_LIST_MAP: SUB_LIST(0,256)(MAP f L) = MAP f (SUB_LIST(0,256) L) *)
       REWRITE_TAC[SUB_LIST_MAP] THEN
       DBG "04m CASE_A after SUB_LIST_MAP" THEN
       (* Build the STACK_CONTENT bridge: SUB_LIST(0,256) niblist is what we care
          about. In Case A, LENGTH niblist = niblen >= 256, so
          STACK_CONTENT niblist = SUB_LIST(0, 256) niblist. *)
       SUBGOAL_THEN
         `SUB_LIST(0, 256) (niblist:int16 list) = STACK_CONTENT niblist`
       SUBST1_TAC THENL
        [CONV_TAC SYM_CONV THEN MATCH_MP_TAC STACK_CONTENT_LARGE THEN
         UNDISCH_TAC `LENGTH(niblist:int16 list) = niblen` THEN
         DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[];
         ALL_TAC] THEN
       DBG "04n CASE_A after STACK_CONTENT_LARGE" THEN
       (* First: establish each b_k = word(num_of_wordlist (SUB_LIST(4k,4) niblist))
          BEFORE LEXPAND. *)
       MP_TAC(GEN `k:num` (ISPECL [`s245:armstate`; `stackpointer:int64`;
                                    `niblist:int16 list`; `k:num`]
                                   BK_FROM_STACK_GE256)) THEN
       ASM_REWRITE_TAC[] THEN
       DISCH_THEN(fun bk_univ ->
         MAP_EVERY (fun i ->
           let inst = SPEC (mk_small_numeral i) bk_univ in
           let premise = EQT_ELIM (NUM_LT_CONV (lhand(concl inst))) in
           ASSUME_TAC (MP inst premise)) (0--63)) THEN
       RULE_ASSUM_TAC(CONV_RULE(DEPTH_CONV NUM_MULT_CONV)) THEN
       RULE_ASSUM_TAC(REWRITE_RULE[WORD_ADD_0]) THEN
       DBG "04o CASE_A after BK facts added + normalized" THEN
       (* BEFORE touching any hyps: build the 64 b_k = word(...) theorems and
          ADD them as hyps via ASSUME_TAC. *)
       (fun (asl, _ as gl) ->
         let bk_trans_thms = List.filter_map (fun (_, th) ->
           let c = concl th in
           if is_eq c then
             let rhs = rand c in
             if is_var rhs && String.length (fst (dest_var rhs)) >= 2 &&
                String.sub (fst (dest_var rhs)) 0 2 = "b_" then
               let lhs = lhand c in
               let bk_fact = List.find_opt (fun (_, th2) ->
                 let c2 = concl th2 in
                 is_eq c2 && lhs = lhand c2 && rhs <> rand c2) asl in
               (match bk_fact with
                | Some (_, bk_th) ->
                  Some (TRANS (SYM th) bk_th)
                | None -> None)
             else None
           else None) asl in
         Printf.printf "DEBUG: bk_trans thms count=%d\n%!"
           (List.length bk_trans_thms);
         MAP_EVERY ASSUME_TAC bk_trans_thms gl) THEN
       DBG "04p CASE_A after 64 b_k=word(...) hyps added" THEN
       (* Now LEXPAND + SPLIT + ASM_REWRITE chains all together. *)
       REWRITE_TAC[ARITH_RULE `1024 = 8 * 128`] THEN
       CONV_TAC(ONCE_DEPTH_CONV BIGNUM_LEXPAND_CONV) THEN
       DBG "04q CASE_A after LEXPAND" THEN
       RULE_ASSUM_TAC(CONV_RULE(ONCE_DEPTH_CONV(READ_MEMORY_SPLIT_CONV 1))) THEN
       DBG "04r CASE_A after bytes128 SPLIT" THEN
       ASM_REWRITE_TAC[] THEN
       DBG "04s CASE_A after ASM_REWRITE chain" THEN
       (* Use the chunk-level BITBLAST identities to collapse the 128 int64
          word_subword expressions. *)
       REWRITE_TAC[SSHLL_CHUNK_WORD_SUBWORD_LO_INT64;
                   SSHLL_CHUNK_WORD_SUBWORD_HI_INT64;
                   SSHLL_CHUNK_WORD_SUBWORD_LO_INT64_HIINNER;
                   SSHLL_CHUNK_WORD_SUBWORD_HI_INT64_HIINNER] THEN
       DBG "04t CASE_A after chunk word_subword collapse (all 4 variants)" THEN
       (* Apply WORD_SUBWORD_JOIN_SUB_LIST_H for a in {0,8,16,...,248} to    *)
       (* reduce each chunk's 8 word_subword(word_join ...) halfword reads   *)
       (* to EL (a+k) niblist. Premise (a+8 <= LENGTH niblist) derives from *)
       (* 256 <= niblen /\ LENGTH niblist = niblen.                         *)
       SUBGOAL_THEN `256 <= LENGTH (niblist:int16 list)` ASSUME_TAC THENL
        [UNDISCH_TAC `LENGTH(niblist:int16 list) = niblen` THEN
         DISCH_THEN SUBST1_TAC THEN
         UNDISCH_TAC `256 <= niblen` THEN REWRITE_TAC[];
         ALL_TAC] THEN
       MP_TAC(GEN `a:num` (ISPECL [`niblist:int16 list`; `a:num`]
                                  WORD_SUBWORD_JOIN_SUB_LIST_H)) THEN
       DISCH_THEN(fun univ_th ->
         MAP_EVERY (fun i ->
           let inst = SPEC (mk_small_numeral i) univ_th in
           let prem_term = lhand(concl inst) in
           let prem_thm = ARITH_RULE(mk_imp(
             `256 <= LENGTH (niblist:int16 list)`, prem_term)) in
           let raw = MATCH_MP inst
             (MP prem_thm (ASSUME `256 <= LENGTH (niblist:int16 list)`)) in
           let discharged = CONV_RULE
             (REWRITE_CONV[ARITH]) raw in
           REWRITE_TAC[discharged])
           (List.map (fun k -> 8 * k) (0--31))) THEN
       DBG "04t2 CASE_A after halfword->EL reduction" THEN
       DUMP_STATE_TAC "/tmp/eta4/case_a_after_04t2.txt" THEN
       (* Unfold STACK_CONTENT on RHS: in Case A, it's SUB_LIST(0,256) niblist. *)
       SUBGOAL_THEN `STACK_CONTENT (niblist:int16 list) = SUB_LIST(0, 256) niblist`
         SUBST1_TAC THENL
        [MATCH_MP_TAC STACK_CONTENT_LARGE THEN ASM_REWRITE_TAC[];
         ALL_TAC] THEN
       DBG "04u1 CASE_A after STACK_CONTENT→SUB_LIST" THEN
       (* Close Case A using PAIR_MAP_IDX_128: the scaled pair-form identity.
          The goal here is exactly of the form
            bignum_of_wordlist [word_join ...; ...(128 entries)...] =
            num_of_wordlist (MAP f (SUB_LIST (0,256) niblist))
          where the word_joins form the byte-pair packing of the filtered
          nibbles, each entry being word_sx(word_sub (word 4) (EL k niblist)). *)
       MATCH_MP_TAC PAIR_MAP_IDX_128 THEN
       ASM_REWRITE_TAC[]]]] THEN

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
         (?lis0 lis1:int16 list.
            LENGTH lis0 <= 8 /\ LENGTH lis1 <= 8 /\
            val(read X12 s:int64) = LENGTH lis0 /\
            val(read X13 s:int64) = LENGTH lis1 /\
            APPEND lis0 lis1 =
              REJ_NIBBLES_ETA4(SUB_LIST(8 * i,8) inlist) /\
            read Q16 s = word(num_of_wordlist lis0):int128 /\
            read Q17 s = word(num_of_wordlist lis1):int128) /\
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
     (* Mirror reference flow: REABBREV idx AFTER FMOV (step 19), ABBREV tab
        BEFORE LDR Q24/Q25 (step 20), so tab0/tab1 equations survive.
        Reference eta4 step mapping:
          step 19 = FMOV W13 (ends X12/X13 popcount first pass)
          step 20 = LDR Q24, step 21 = LDR Q25
          step 22 = CNT Q4, step 23 = CNT Q5
          step 24 = UADDLV Q20, step 25 = UADDLV Q21
          step 26 = FMOV W12, step 27 = FMOV W13
          step 28 = TBL Q16, step 29 = TBL Q17 *)
     MAP_EVERY REABBREV_TAC
      [`idx0 = read X12 s19`; `idx1 = read X13 s19`] THEN
     MAP_EVERY ABBREV_TAC
      [`tab0 = read(memory :> bytes128(word_add table
                   (word(16 * val(idx0:int64))))) s19`;
       `tab1 = read(memory :> bytes128(word_add table
                   (word(16 * val(idx1:int64))))) s19`] THEN
     (* Steps 20-27: LDR+CNT+UADDLV+FMOV (no TBL yet). *)
     ARM_STEPS_TAC MLDSA_REJ_UNIFORM_ETA4_EXEC (20--27) THEN
     RULE_ASSUM_TAC(REWRITE_RULE[WORD_SUBWORD_AND]) THEN
     RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV)) THEN
     RULE_ASSUM_TAC(CONV_RULE WORD_REDUCE_CONV) THEN
     RULE_ASSUM_TAC(REWRITE_RULE
      [word_ugt; relational2; GT; WORD_AND_MASK]) THEN
     RULE_ASSUM_TAC(ONCE_REWRITE_RULE[COND_RAND]) THEN
     RULE_ASSUM_TAC(CONV_RULE WORD_REDUCE_CONV) THEN
     (* Steps 28-29: TBL Q16, TBL Q17. *)
     ARM_STEPS_TAC MLDSA_REJ_UNIFORM_ETA4_EXEC (28--29) THEN
     DBG "10 after steps 1-29" THEN
     (* Reference-style TBL correctness lemma: prove Q16 s29 / Q17 s29 content
        from table content + nibbles identities, BEFORE ENSURES_FINAL_STATE_TAC
        so that the state tracking for Q16/Q17 reads is still live. *)
     SUBGOAL_THEN
       `read Q16 s29 = word(num_of_wordlist
                            (REJ_NIBBLES_ETA4
                              [word_subword (loaded_d:int64) (0,8):byte;
                               word_subword loaded_d (8,8);
                               word_subword loaded_d (16,8);
                               word_subword loaded_d (24,8)])) /\
        read Q17 s29 = word(num_of_wordlist
                            (REJ_NIBBLES_ETA4
                              [word_subword (loaded_d:int64) (32,8):byte;
                               word_subword loaded_d (40,8);
                               word_subword loaded_d (48,8);
                               word_subword loaded_d (56,8)]))`
     MP_TAC THENL
      [(* Establish the 16 halfword identities inline: nibbles_k halfwords
           are word_zx of byte-nibble expressions. *)
       REWRITE_TAC[UADDLV_COUNT_LEMMA] THEN
       REWRITE_TAC(List.map (fun k -> BITBLAST_RULE
         (vsubst [mk_small_numeral k, `k:num`]
         `bit k (word_subword (word_neg (word (bitval b):16 word))
                 (0,8):8 word) <=> b`)) (0--7)) THEN
       ASM_REWRITE_TAC[] THEN
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
       (* Apply byte-split lemmas (defined in preamble) to derive 32
          byte-level identities from the 16 halfword identities.  Each
          BYTE_SPLIT_{AND,USHR}.(k) has form
            !x b. word_subword x (k*16,16) = word_zx(<AND|USHR> b ...)
                  ==> word_subword x (k*16,8) = <AND|USHR> b ... /\
                      word_subword x (k*16+8,8) = word 0
          Apply via `MATCH_MP` against each assumption — the 16 halfword
          identities produce the 16 strip pairs (32 byte-level facts). *)
       (* Use MATCH_MP to apply each byte-split lemma to every matching
          halfword identity assumption.  Collect all 32 byte-level facts,
          then add them via MAP_EVERY ASSUME_TAC. *)
       (fun (asl, w) ->
          let halfword_hyps =
            List.filter (fun (_,th) ->
              let c = concl th in
              is_eq c &&
              (try let l = lhand c in
                   match l with
                   | Comb(Comb(Const("word_subword",_), v),
                          Comb(Comb(Const(",",_), _), len_tm)) ->
                       is_var v &&
                       (let nm = fst(dest_var v) in
                        nm = "nibbles0" || nm = "nibbles1b") &&
                       (try dest_small_numeral len_tm = 16 with _ -> false)
                   | _ -> false
               with _ -> false)) asl in
          let byte_lemmas = BYTE_SPLIT_AND @ BYTE_SPLIT_USHR in
          let new_facts = List.concat (List.map (fun (_, h) ->
            List.concat (List.map (fun lem ->
              try CONJUNCTS(MATCH_MP lem h)
              with _ -> []) byte_lemmas)) halfword_hyps) in
          (MAP_EVERY ASSUME_TAC new_facts) (asl, w)) THEN
       UNDISCH_TAC
        `read(memory :> bytes(table,4096)) s29 =
         num_of_wordlist mldsa_rej_uniform_eta_table` THEN
       REPLICATE_TAC 4
        (GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV)
              [GSYM NUM_OF_PAIR_WORDLIST]) THEN
       REWRITE_TAC[mldsa_rej_uniform_eta_table; pair_wordlist] THEN
       CONV_TAC WORD_REDUCE_CONV THEN
       CONV_TAC(LAND_CONV BYTES_EQ_NUM_OF_WORDLIST_EXPAND_CONV) THEN
       REWRITE_TAC[GSYM BYTES128_WBYTES] THEN REPEAT STRIP_TAC THEN
       DISCARD_MATCHING_ASSUMPTIONS
        [`read Q24 s = x`; `read Q25 s = x`] THEN
       REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check
         (fun th -> is_var(rhs(concl th)) &&
                    let n = fst(dest_var(rhs(concl th))) in
                    n = "tab0" || n = "tab1"))) THEN
       DISCARD_MATCHING_ASSUMPTIONS
        [`read X12 s = x`; `read X13 s = x`] THEN
       REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check
         (fun th -> is_var(rhs(concl th)) &&
                    let n = fst(dest_var(rhs(concl th))) in
                    n = "idx0" || n = "idx1"))) THEN
       ASM_REWRITE_TAC[] THEN
       DISCARD_MATCHING_ASSUMPTIONS
        [`read Q16 s = x`; `read Q17 s = x`] THEN
       (* Unfold REJ_NIBBLES_ETA4 -> FILTER + NIBBLES_OF_BYTES on the 4
          concrete byte-subwords, then FILTER itself, so the 8 `val x < 9`
          conditions become concrete ifs with x = word(val b_k MOD/DIV 16). *)
       REWRITE_TAC[REJ_NIBBLES_ETA4; NIBBLES_OF_BYTES; NIBBLE_PAIR; APPEND] THEN
       REWRITE_TAC[FILTER] THEN
       (* Normalize val(word_zx(word_and/ushr ...)) on both LHS (TBL output
          conditions) and RHS (FILTER predicate) so they share the same form
          val(word_subword loaded_d (k,8)) MOD/DIV 16 < 9. *)
       REWRITE_TAC[VAL_WORD_ZX_BYTE16; BYTE_AND_15_MOD; BYTE_USHR4_DIV;
                   VAL_WORD_NIBBLE_LT] THEN
       REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN
       REWRITE_TAC[BITVAL_CLAUSES] THEN
       CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV) THEN
       CONV_TAC NUM_REDUCE_CONV THEN
       (* Normalize word_add table (word 0) = table and apply the 256 bytes128
          hypotheses to substitute concrete int128 table-entry values. *)
       REWRITE_TAC[WORD_ADD_0] THEN
       ASM_REWRITE_TAC[] THEN
       (* Reduce word_subword of constant int128 values to constant bytes,
          then val, then reduce the 8*val computation.  Also unfold
          num_of_wordlist on the concrete filtered list on RHS. *)
       CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
       CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV) THEN
       CONV_TAC NUM_REDUCE_CONV THEN
       REWRITE_TAC[num_of_wordlist; MULT_CLAUSES; ADD_CLAUSES] THEN
       CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV) THEN
       RULE_ASSUM_TAC(REWRITE_RULE[BYTE_AND_15_MOD; BYTE_USHR4_DIV;
                                   VAL_WORD_ZX_BYTE16; VAL_WORD_NIBBLE_LT]) THEN
       ASM_REWRITE_TAC[] THEN
       REWRITE_TAC[VAL_WORD; DIMINDEX_16] THEN
       CONV_TAC NUM_REDUCE_CONV THEN
       REWRITE_TAC[VAL_BYTE_NIB_MOD_65536] THEN
       CONV_TAC WORD_BLAST;
       STRIP_TAC] THEN
     DBG "10a after TBL correctness subgoal" THEN
     (* Discard the ARM stepper's Q16/Q17 word_join form — we have the clean
        equation from the SUBGOAL (read Q16/Q17 s29 = word(num_of_wordlist ...))
        and the nested word_join version only causes ASM_REWRITE_TAC to rewrite
        the goal into an un-closable shape. *)
     DISCARD_MATCHING_ASSUMPTIONS
      [`read Q16 s = word_join (x:int64) (y:int64):int128`;
       `read Q17 s = word_join (x:int64) (y:int64):int128`] THEN
     DBG "10a2 after DISCARD arm Q16/Q17 word_join" THEN
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
     TRY(ASM_REWRITE_TAC[] THEN NO_TAC) THEN
     TRY(ASM_ARITH_TAC) THEN
     (* Remaining goal: the existential `?lis0 lis1. ...` carrying post-TBL
        Q16/Q17 content. Witness lis0/lis1 explicitly as the filtered nibbles
        of the first/second halves of loaded_d. Then LENGTH bounds and APPEND
        decomposition close directly; only the TBL-semantic Q16/Q17/X12/X13
        equalities remain as a CHEAT (TBL correctness on the 256-entry
        eta table). *)
     DBG "14 first-half existential" THEN
     DUMP_STATE_TAC "/tmp/eta4/cheat_tbl_state_pre.txt" THEN
     EXISTS_TAC
       `REJ_NIBBLES_ETA4
          [word_subword (loaded_d:int64) (0,8):byte;
           word_subword loaded_d (8,8);
           word_subword loaded_d (16,8);
           word_subword loaded_d (24,8)]` THEN
     EXISTS_TAC
       `REJ_NIBBLES_ETA4
          [word_subword (loaded_d:int64) (32,8):byte;
           word_subword loaded_d (40,8);
           word_subword loaded_d (48,8);
           word_subword loaded_d (56,8)]` THEN
     DBG "14a after EXISTS_TAC witnesses" THEN
     (* LENGTH bounds: LENGTH(REJ_NIBBLES_ETA4[4 bytes]) <= 8. *)
     REWRITE_TAC[REJ_NIBBLES_ETA4_LENGTH_4] THEN
     DBG "14b after LENGTH bounds" THEN
     (* Derive SUB_LIST(8*i, 8) inlist = [word_subword loaded_d (0,8); ...;
        (56,8)] from the memory-loaded bytes hypothesis. *)
     SUBGOAL_THEN
       `SUB_LIST(8 * i, 8) (inlist:byte list) =
        [word_subword (loaded_d:int64) (0,8):byte;
         word_subword loaded_d (8,8);
         word_subword loaded_d (16,8);
         word_subword loaded_d (24,8);
         word_subword loaded_d (32,8);
         word_subword loaded_d (40,8);
         word_subword loaded_d (48,8);
         word_subword loaded_d (56,8)]`
     ASSUME_TAC THENL
      [DBG "14b1 start SUB_LIST bridge" THEN
       CONV_TAC SYM_CONV THEN
       REWRITE_TAC[LISTS_NUM_OF_WORDLIST_EQ] THEN CONJ_TAC THENL
        [REWRITE_TAC[LENGTH; LENGTH_SUB_LIST] THEN
         UNDISCH_TAC `LENGTH(inlist:byte list) = buflen` THEN
         UNDISCH_TAC `8 * (i + 1) <= buflen` THEN ARITH_TAC;
         ALL_TAC] THEN
       REWRITE_TAC[NUM_OF_WORDLIST_SUB_LIST; DIMINDEX_8] THEN
       MP_TAC(ASSUME `read (memory :> bytes (buf,buflen)) s29 =
                      num_of_wordlist (inlist:byte list)`) THEN
       DISCH_THEN(MP_TAC o AP_TERM
         `\x. x DIV 2 EXP (8 * 8 * i) MOD 2 EXP (8 * 8)`) THEN
       CONV_TAC(ONCE_DEPTH_CONV BETA_CONV) THEN
       REWRITE_TAC[READ_COMPONENT_COMPOSE;
                   READ_BYTES_DIV; READ_BYTES_MOD] THEN
       SUBGOAL_THEN `MIN (buflen - 8 * i) 8 = 8` SUBST1_TAC THENL
        [UNDISCH_TAC `8 * (i + 1) <= buflen` THEN ARITH_TAC;
         ALL_TAC] THEN
       MP_TAC(ISPECL
         [`word_add buf (word (8 * i)):int64`; `read memory s29`]
         (INST_TYPE[`:64`,`:N`] VAL_READ_WBYTES)) THEN
       REWRITE_TAC[DIMINDEX_64] THEN CONV_TAC NUM_REDUCE_CONV THEN
       REWRITE_TAC[GSYM BYTES64_WBYTES; GSYM READ_COMPONENT_COMPOSE] THEN
       ASM_REWRITE_TAC[] THEN
       DISCH_THEN(ASSUME_TAC o SYM) THEN DISCH_TAC THEN
       SUBGOAL_THEN
        `num_of_wordlist
          [(word_subword (loaded_d:int64) (0,8):byte);
           (word_subword loaded_d (8,8):byte);
           (word_subword loaded_d (16,8):byte);
           (word_subword loaded_d (24,8):byte);
           (word_subword loaded_d (32,8):byte);
           (word_subword loaded_d (40,8):byte);
           (word_subword loaded_d (48,8):byte);
           (word_subword loaded_d (56,8):byte)] =
         val(loaded_d:int64)` SUBST1_TAC THENL
        [REWRITE_TAC[num_of_wordlist; DIMINDEX_8] THEN
         CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC WORD_BLAST;
         ASM_MESON_TAC[]];
       ALL_TAC] THEN
     DBG "14b2 after SUB_LIST bridge" THEN
     (* Rewrite the target list via the SUB_LIST bridge and decompose via
        REJ_NIBBLES_ETA4_SPLIT_8 to close the APPEND conjunct. *)
     ASM_REWRITE_TAC[REJ_NIBBLES_ETA4_SPLIT_8] THEN
     DBG "14b3 after ASM_REWRITE SPLIT_8" THEN
     (* Establish the 16 halfword identities ONCE at the top (instead of
        inside TRY per conjunct). These are: word_subword nibbles0 (k*16,16)
        = word_zx(nibble_k of loaded_d's first 4 bytes), and analogously
        for nibbles1b's second 4 bytes. *)
     REWRITE_TAC[UADDLV_COUNT_LEMMA] THEN
     REWRITE_TAC(List.map (fun k -> BITBLAST_RULE
       (vsubst [mk_small_numeral k, `k:num`]
       `bit k (word_subword (word_neg (word (bitval b):16 word))
               (0,8):8 word) <=> b`)) (0--7)) THEN
     DBG "14b4 after bit-k rewrites" THEN
     ASM_REWRITE_TAC[] THEN
     DBG "14b5 after ASM_REWRITE" THEN
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
     DBG "14b6 after prove_hw 16x" THEN
     (* Now split conjuncts and close each one. *)
     REPEAT CONJ_TAC THEN
     DBG "14c after REPEAT CONJ_TAC" THEN
     (* Close each subgoal. FIRST-tries all 4 tactic branches per subgoal,
        so only one matches each shape. *)
     FIRST
      [(* X12/X13 val-to-LENGTH: COUNT_BRIDGE_ABSTRACT_4 on nibbles0 *)
       MP_TAC(SPECL
        [`nibbles0:int128`;
         `word_subword (loaded_d:int64) (0,8):byte`;
         `word_subword (loaded_d:int64) (8,8):byte`;
         `word_subword (loaded_d:int64) (16,8):byte`;
         `word_subword (loaded_d:int64) (24,8):byte`] COUNT_BRIDGE_ABSTRACT_4) THEN
       ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
       DISCH_THEN SUBST1_TAC THEN REFL_TAC;
       MP_TAC(SPECL
        [`nibbles1b:int128`;
         `word_subword (loaded_d:int64) (32,8):byte`;
         `word_subword (loaded_d:int64) (40,8):byte`;
         `word_subword (loaded_d:int64) (48,8):byte`;
         `word_subword (loaded_d:int64) (56,8):byte`] COUNT_BRIDGE_ABSTRACT_4) THEN
       ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
       DISCH_THEN SUBST1_TAC THEN REFL_TAC;
       (* Q16 / Q17: goal is `word_join(<TBL>) = word(num_of_wordlist(...))`.
          My SUBGOAL_THEN provided `read Q16/Q17 s29 = word(num_of_wordlist(...))`.
          ARM stepper provided `read Q16/Q17 s29 = <word_join expression>`.
          TRANS these two (after SYM on one) to get the desired equality. *)
       (DUMP_STATE_TAC "/tmp/eta4/q16_tbl_goal.txt" THEN
        FIRST_ASSUM(fun my_hyp ->
          FIRST_ASSUM(fun arm_hyp ->
            try ACCEPT_TAC(TRANS (SYM arm_hyp) my_hyp)
            with _ -> NO_TAC)))];
     DBG "14e after FIRST branches" THEN
     ALL_TAC] THEN
   (* Second half: ST1 stores + accumulation — 6 steps *)
   DBG "15 second half start" THEN
   ENSURES_INIT_TAC "s0" THEN
   DBG "15a after ENSURES_INIT" THEN
   (* Unpack ?lis0 lis1 from the strengthened invariant. *)
   FIRST_X_ASSUM(X_CHOOSE_THEN `lis0:int16 list` MP_TAC o check
     (fun th -> try fst(dest_var(fst(dest_exists(concl th)))) = "lis0"
                with _ -> false)) THEN
   DISCH_THEN(X_CHOOSE_THEN `lis1:int16 list` STRIP_ASSUME_TAC) THEN
   DBG "15a2 after CHOOSE lis0/lis1" THEN
   ABBREV_TAC `len0 = LENGTH(lis0:int16 list)` THEN
   ABBREV_TAC `len1 = LENGTH(lis1:int16 list)` THEN
   DBG "15b after ABBREV len0/len1" THEN
   (* Promote val(X12 s0) = len0, val(X13 s0) = len1 (from invariant). *)
   SUBGOAL_THEN `val(read X12 s0:int64) = len0 /\ val(read X13 s0:int64) = len1`
     STRIP_ASSUME_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
   DBG "15b2 after val(X12/X13 s0) = len_i" THEN
   (* Step 1 = ST1 Q16 at X7 = sp+2*curlen. After step, bytes128 at that
      address holds word(num_of_wordlist lis0). *)
   ARM_STEPS_TAC MLDSA_REJ_UNIFORM_ETA4_EXEC [1] THEN
   DBG "15c after ARM step 1 (STR Q16)" THEN
   (* Establish memory equation covering APPEND curlist lis0. *)
   SUBGOAL_THEN
    `read (memory :> bytes (stackpointer, 2 * (curlen + len0))) s1 =
     num_of_wordlist(APPEND curlist lis0:int16 list)`
   ASSUME_TAC THENL
    [REWRITE_TAC[LEFT_ADD_DISTRIB] THEN
     DBG "WB1a before LENGTH curlist" THEN
     SUBGOAL_THEN `LENGTH(curlist:int16 list) = curlen` ASSUME_TAC THENL
      [EXPAND_TAC "curlen" THEN REFL_TAC; ALL_TAC] THEN
     DBG "WB1b after LENGTH curlist" THEN
     W(MP_TAC o PART_MATCH (lhand o rand)
       BYTES_EQ_NUM_OF_WORDLIST_APPEND o snd) THEN
     DBG "WB1c after PART_MATCH" THEN
     ANTS_TAC THENL
      [REWRITE_TAC[DIMINDEX_16] THEN ASM_REWRITE_TAC[] THEN ARITH_TAC;
       ALL_TAC] THEN
     DBG "WB1d after ANTS" THEN
     DISCH_THEN SUBST1_TAC THEN
     DBG "WB1e after SUBST1 iff" THEN
     CONJ_TAC THENL
      [ASM_REWRITE_TAC[];
       DBG "WB1f in second CONJ" THEN
       SUBGOAL_THEN
        `read (memory :> bytes128
               (word_add stackpointer (word (2 * curlen)))) s1 =
         word(num_of_wordlist(lis0:int16 list)):int128`
       MP_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
       DBG "WB1g after bytes128 SUBGOAL" THEN
       DISCH_THEN(MP_TAC o AP_TERM `val:int128->num`) THEN
       REWRITE_TAC[READ_COMPONENT_COMPOSE; BYTES128_WBYTES;
                   VAL_READ_WBYTES;
                   DIMINDEX_128; ARITH_RULE `128 DIV 8 = 16`] THEN
       DBG "WB1h after WBYTES rewrites" THEN
       SUBGOAL_THEN `2 * len0 = MIN 16 (2 * len0)` SUBST1_TAC THENL
        [UNDISCH_TAC `len0:num <= 8` THEN ARITH_TAC;
         REWRITE_TAC[GSYM READ_BYTES_MOD]] THEN
       DBG "WB1i after MIN subst" THEN
       DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[VAL_WORD] THEN
       REWRITE_TAC[DIMINDEX_128; MOD_MOD_EXP_MIN] THEN
       MATCH_MP_TAC MOD_LT THEN
       MATCH_MP_TAC NUM_OF_WORDLIST_BOUND_GEN THEN
       ASM_REWRITE_TAC[DIMINDEX_16] THEN
       UNDISCH_TAC `len0:num <= 8` THEN ARITH_TAC];
     ALL_TAC] THEN
   DBG "15c2 after memory curlist+lis0 at s1" THEN
   SUBGOAL_THEN `read X12 s1:int64 = word len0` ASSUME_TAC THENL
    [REWRITE_TAC[GSYM VAL_EQ] THEN ASM_REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN
     CONV_TAC SYM_CONV THEN MATCH_MP_TAC MOD_LT THEN
     UNDISCH_TAC `len0:num <= 8` THEN ARITH_TAC; ALL_TAC] THEN
   SUBGOAL_THEN `read X13 s1:int64 = word len1` ASSUME_TAC THENL
    [REWRITE_TAC[GSYM VAL_EQ] THEN ASM_REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN
     CONV_TAC SYM_CONV THEN MATCH_MP_TAC MOD_LT THEN
     UNDISCH_TAC `len1:num <= 8` THEN ARITH_TAC; ALL_TAC] THEN
   DBG "15h after X12/X13 s1" THEN
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
   (* Reduce val(word len0) → len0 in hypotheses so the ST1 Q17 step
      records the clean address. *)
   SUBGOAL_THEN `val(word len0:int64) = len0` ASSUME_TAC THENL
    [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN
     UNDISCH_TAC `len0:num <= 8` THEN ARITH_TAC; ALL_TAC] THEN
   RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `val(word len0:int64) = len0`]) THEN
   (* Step 3 = ST1 Q17 at X7 = sp+2*(curlen+len0). *)
   ARM_STEPS_TAC MLDSA_REJ_UNIFORM_ETA4_EXEC [3] THEN
   DBG "15l after ARM step 3 (STR Q17)" THEN
   (* Reduce val(word len0) → len0 again (ARM_STEPS re-introduces it). *)
   RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `val(word len0:int64) = len0`]) THEN
   (* Build memory equation covering APPEND (APPEND curlist lis0) lis1. *)
   SUBGOAL_THEN
    `read (memory :> bytes (stackpointer, 2 * ((curlen + len0) + len1))) s3 =
     num_of_wordlist(APPEND (APPEND curlist lis0) lis1:int16 list)`
   ASSUME_TAC THENL
    [REWRITE_TAC[LEFT_ADD_DISTRIB] THEN
     DBG "WB2a start" THEN
     DUMP_STATE_TAC "/tmp/eta4/wb2_start.txt" THEN
     SUBGOAL_THEN
       `LENGTH(APPEND curlist lis0:int16 list) = curlen + len0`
     ASSUME_TAC THENL
      [REWRITE_TAC[LENGTH_APPEND] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
     DBG "WB2b after LENGTH APPEND" THEN
     W(MP_TAC o PART_MATCH (lhand o rand)
       BYTES_EQ_NUM_OF_WORDLIST_APPEND o snd) THEN
     DBG "WB2c after PART_MATCH" THEN
     ANTS_TAC THENL
      [REWRITE_TAC[DIMINDEX_16] THEN ASM_REWRITE_TAC[] THEN ARITH_TAC;
       ALL_TAC] THEN
     DBG "WB2d after ANTS" THEN
     DISCH_THEN SUBST1_TAC THEN
     DBG "WB2e after SUBST1" THEN
     (* Normalize split address so it matches the hyp. *)
     SUBGOAL_THEN
       `word_add stackpointer (word (2 * curlen + 2 * len0):int64) =
        word_add stackpointer (word (2 * (curlen + len0)))`
      (fun th -> REWRITE_TAC[th]) THENL
      [CONV_TAC WORD_RULE; ALL_TAC] THEN
     SUBGOAL_THEN `2 * curlen + 2 * len0 = 2 * (curlen + len0)`
      SUBST1_TAC THENL [ARITH_TAC; ALL_TAC] THEN
     CONJ_TAC THENL
      [ASM_REWRITE_TAC[];
       DBG "WB2f in second CONJ" THEN
       DUMP_STATE_TAC "/tmp/eta4/wb2_second_conj.txt" THEN
       SUBGOAL_THEN
        `read (memory :> bytes128
               (word_add stackpointer (word (2 * (curlen + len0))))) s3 =
         word(num_of_wordlist(lis1:int16 list)):int128`
       MP_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
       DBG "WB2g after bytes128" THEN
       DISCH_THEN(MP_TAC o AP_TERM `val:int128->num`) THEN
       REWRITE_TAC[READ_COMPONENT_COMPOSE; BYTES128_WBYTES;
                   VAL_READ_WBYTES;
                   DIMINDEX_128; ARITH_RULE `128 DIV 8 = 16`] THEN
       DBG "WB2h after WBYTES rewrites" THEN
       SUBGOAL_THEN `2 * len1 = MIN 16 (2 * len1)` SUBST1_TAC THENL
        [UNDISCH_TAC `len1:num <= 8` THEN ARITH_TAC;
         REWRITE_TAC[GSYM READ_BYTES_MOD]] THEN
       DBG "WB2i after MIN subst" THEN
       DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[VAL_WORD] THEN
       REWRITE_TAC[DIMINDEX_128; MOD_MOD_EXP_MIN] THEN
       MATCH_MP_TAC MOD_LT THEN
       MATCH_MP_TAC NUM_OF_WORDLIST_BOUND_GEN THEN
       ASM_REWRITE_TAC[DIMINDEX_16] THEN
       UNDISCH_TAC `len1:num <= 8` THEN ARITH_TAC];
     ALL_TAC] THEN
   DBG "15l2 after memory curlist+lis0+lis1 at s3" THEN
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
   (* newbatch = APPEND lis0 lis1 from invariant *)
   SUBGOAL_THEN `APPEND (lis0:int16 list) lis1 = newbatch` ASSUME_TAC THENL
    [EXPAND_TAC "newbatch" THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
   SUBGOAL_THEN `LENGTH(newbatch:int16 list) = len0 + len1` ASSUME_TAC THENL
    [UNDISCH_TAC `APPEND (lis0:int16 list) lis1 = newbatch` THEN
     DISCH_THEN(SUBST1_TAC o SYM) THEN
     REWRITE_TAC[LENGTH_APPEND] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
   (* val(word len_i) = len_i reductions — simplify register forms. *)
   SUBGOAL_THEN `val(word len0:int64) = len0 /\ val(word len1:int64) = len1`
     STRIP_ASSUME_TAC THENL
    [CONJ_TAC THEN MATCH_MP_TAC VAL_WORD_EQ THEN
     REWRITE_TAC[DIMINDEX_64] THENL
      [UNDISCH_TAC `len0:num <= 8` THEN ARITH_TAC;
       UNDISCH_TAC `len1:num <= 8` THEN ARITH_TAC];
     ALL_TAC] THEN
   REWRITE_TAC[LENGTH_APPEND] THEN ASM_REWRITE_TAC[] THEN
   DBG "15v after newbatch decomp" THEN
   REPEAT CONJ_TAC THEN
   DBG "15w after REPEAT CONJ_TAC" THEN
   TRY(CONV_TAC WORD_RULE) THEN
   DBG "15x after TRY WORD_RULE" THEN
   TRY(AP_TERM_TAC THEN AP_TERM_TAC THEN
       ASM_REWRITE_TAC[] THEN ARITH_TAC) THEN
   DBG "15y after TRY size-equality" THEN
   (* Remaining: the memory-APPEND goal. Close via the established
      curlist+lis0+lis1 memory equation (now propagated to s6 by MAYCHANGE). *)
   DUMP_STATE_TAC "/tmp/eta4/cheat3_final.txt" THEN
   SUBGOAL_THEN
     `2 * (curlen + len0 + len1) = 2 * ((curlen + len0) + len1)`
    SUBST1_TAC THENL [ARITH_TAC; ALL_TAC] THEN
   SUBGOAL_THEN
     `APPEND curlist (newbatch:int16 list) =
      APPEND (APPEND curlist lis0) lis1`
    SUBST1_TAC THENL
     [UNDISCH_TAC `APPEND (lis0:int16 list) lis1 = newbatch` THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN
      REWRITE_TAC[APPEND_ASSOC]; ALL_TAC] THEN
   ASM_REWRITE_TAC[];

   (*** Subgoal 4: Back edge — 2 ARM steps from pc+248 to pc+108 ***)
   DBG "16 subgoal4 back edge" THEN
   X_GEN_TAC `i:num` THEN STRIP_TAC THEN
   CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
   DBG "16a after let_CONV" THEN
   ENSURES_INIT_TAC "s0" THEN
   DBG "16b after ENSURES_INIT" THEN
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
   DBG "16c after 8<=val subgoal" THEN
   ARM_STEPS_TAC MLDSA_REJ_UNIFORM_ETA4_EXEC (1--2) THEN
   DBG "16d after ARM 1-2" THEN
   ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[];

   (*** Subgoal 5: Post-loop exit — from pc+248 to pc+256 ***)
   (*** WOP: at i=N, either buffer exhausted or 256 <= niblen ***)
   DBG "17 subgoal5 post-loop" THEN
   CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
   DBG "17a after let_CONV" THEN
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
   DBG "17b after niblen setup" THEN
   ASM_CASES_TAC `256 <= niblen` THENL
    [(* Case: 256 <= niblen — enough samples *)
     DBG "17c niblen>=256 case" THEN
     ASM_CASES_TAC `8 <= val(word_sub (word buflen:int64) (word(8 * N)))` THENL
      [(* Subcase: X2 >= 8 — back edge branches to pc+108, then CMP X9>=X4 *)
       DBG "17d X2>=8 subcase" THEN
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
         DBG "17e firsthalf 248->108" THEN
         ENSURES_INIT_TAC "s0" THEN
         DBG "17e1 after ENSURES_INIT" THEN
         ARM_STEPS_TAC MLDSA_REJ_UNIFORM_ETA4_EXEC (1--2) THEN
         DBG "17e2 after ARM 1-2" THEN
         ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
         DBG "17e3 after FINAL+ASM_REWRITE" THEN
         REWRITE_TAC[ALL] THEN ASM_REWRITE_TAC[] THEN
         CONJ_TAC THENL [NONOVERLAPPING_TAC; NONOVERLAPPING_TAC];
         (* pc+108 -> pc+256: CMP X9,X4; BCS forward since X9=niblen>=256 *)
         DBG "17f secondhalf 108->256" THEN
         ENSURES_INIT_TAC "s0" THEN
         DBG "17f1 after ENSURES_INIT" THEN
         SUBGOAL_THEN `256 <= val(word niblen:int64)` ASSUME_TAC THENL
          [REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN
           SUBGOAL_THEN `niblen MOD 2 EXP 64 = niblen` SUBST1_TAC THENL
            [MATCH_MP_TAC MOD_LT THEN UNDISCH_TAC `niblen < 272` THEN
             ARITH_TAC;
             ASM_REWRITE_TAC[]];
           ALL_TAC] THEN
         ARM_STEPS_TAC MLDSA_REJ_UNIFORM_ETA4_EXEC (1--2) THEN
         DBG "17f2 after ARM 1-2" THEN
         ENSURES_FINAL_STATE_TAC THEN
         DBG "17f3 after FINAL" THEN
         REWRITE_TAC[ALL] THEN ASM_REWRITE_TAC[] THEN
         DBG "17f4 after REWRITE ALL" THEN
         EXISTS_TAC `N:num` THEN
         CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN ASM_REWRITE_TAC[] THEN
         DBG "17f5 after EXISTS+let_CONV" THEN
         UNDISCH_TAC `niblen < 272` THEN EXPAND_TAC "niblen" THEN
         ARITH_TAC];
       (* Subcase: X2 < 8 — falls through *)
       DBG "17g X2<8 subcase" THEN
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
