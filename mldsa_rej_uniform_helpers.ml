(* Helper lemmas for mldsa_rej_uniform proof - VMOVMSKPS+POPCNT chain *)

(* word_popcount is preserved through word_zx *)
let WORD_POPCOUNT_WORD_ZX = prove
 (`!(w:N word). dimindex(:N) <= dimindex(:M) ==> word_popcount(word_zx w:M word) = word_popcount w`,
  GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[word_popcount] THEN AP_TERM_TAC THEN
  REWRITE_TAC[EXTENSION; IN_ELIM_THM; bits_of_word; BIT_WORD_ZX] THEN
  X_GEN_TAC `j:num` THEN EQ_TAC THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  ASM_MESON_TAC[BIT_TRIVIAL; NOT_LT; LTE_TRANS]);;

(* word_of_bits VMOVMSKPS pattern = sum of bitvals *)
let VMOVMSKPS_BYTE_EQ = prove
 (`!x:int256. word_of_bits(\i. i < 8 /\ bit(32*i+31) x):byte =
   word(bitval(bit 31 x) + 2 * bitval(bit 63 x) + 4 * bitval(bit 95 x) +
        8 * bitval(bit 127 x) + 16 * bitval(bit 159 x) + 32 * bitval(bit 191 x) +
        64 * bitval(bit 223 x) + 128 * bitval(bit 255 x))`,
  GEN_TAC THEN
  REWRITE_TAC[WORD_OF_BITS_AS_WORD_ALT; DIMINDEX_8] THEN
  CONV_TAC NUM_REDUCE_CONV THEN AP_TERM_TAC THEN
  CONV_TAC(LAND_CONV EXPAND_NSUM_CONV) THEN
  REWRITE_TAC[IN] THEN CONV_TAC(DEPTH_CONV BETA_CONV) THEN
  CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC);;

(* bit(32*k+31)(x:int256) = bit 31(word_subword x (32*k,32):int32) *)
let BIT_SUBWORD_256 = prove
 ((rand o concl o (EXPAND_CASES_CONV THENC NUM_REDUCE_CONV))
  `!i. i < 8 ==>
    !x:int256. bit(32*i+31) x = bit 31 (word_subword x (32*i,32):int32)`,
  CONV_TAC WORD_BLAST);;

(* Combined: word_popcount of word_of_bits = word_popcount of bitval sum *)
let VMOVMSKPS_POPCOUNT_EQ = prove
 (`!x:int256.
   word_popcount(word_of_bits(\i. i < 8 /\ bit(32*i+31) x):byte) =
   word_popcount(word(
     bitval(bit 31 (word_subword x (0,32):int32)) +
     2 * bitval(bit 31 (word_subword x (32,32):int32)) +
     4 * bitval(bit 31 (word_subword x (64,32):int32)) +
     8 * bitval(bit 31 (word_subword x (96,32):int32)) +
     16 * bitval(bit 31 (word_subword x (128,32):int32)) +
     32 * bitval(bit 31 (word_subword x (160,32):int32)) +
     64 * bitval(bit 31 (word_subword x (192,32):int32)) +
     128 * bitval(bit 31 (word_subword x (224,32):int32))):byte)`,
  GEN_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[VMOVMSKPS_BYTE_EQ; BIT_SUBWORD_256]);;

(* Extract bit 31 from each lane of nested word_join of int32's *)
let BIT_NESTED_JOIN_8 = REWRITE_RULE[LET_DEF; LET_END_DEF] (prove
 (`!(a0:int32) (a1:int32) (a2:int32) (a3:int32) (a4:int32) (a5:int32) (a6:int32) (a7:int32).
   let x:int256 = word_join
     (word_join (word_join a7 a6:int64) (word_join a5 a4:int64):int128)
     (word_join (word_join a3 a2:int64) (word_join a1 a0:int64):int128) in
   bit 31 (word_subword x (0,32):int32) = bit 31 a0 /\
   bit 31 (word_subword x (32,32):int32) = bit 31 a1 /\
   bit 31 (word_subword x (64,32):int32) = bit 31 a2 /\
   bit 31 (word_subword x (96,32):int32) = bit 31 a3 /\
   bit 31 (word_subword x (128,32):int32) = bit 31 a4 /\
   bit 31 (word_subword x (160,32):int32) = bit 31 a5 /\
   bit 31 (word_subword x (192,32):int32) = bit 31 a6 /\
   bit 31 (word_subword x (224,32):int32) = bit 31 a7`,
  REPEAT GEN_TAC THEN CONV_TAC let_CONV THEN
  REWRITE_TAC[BIT_WORD_SUBWORD; BIT_WORD_JOIN;
              DIMINDEX_32; DIMINDEX_64; DIMINDEX_128; DIMINDEX_256] THEN
  CONV_TAC NUM_REDUCE_CONV));;

(* Byte shuffle extraction: extracting 3 consecutive bytes + zero pad
   gives the 24-bit zero-extended coefficient.
   Low lane (coefficients 0-3 from 128-bit source): *)
let SHUFFLE_LOW_LANE = prove
 ((rand o concl o (EXPAND_CASES_CONV THENC NUM_REDUCE_CONV))
  `!k. k < 4 ==>
    !x:int128.
      word_join (word 0:byte)
        (word_join (word_subword x (24*k+16, 8):byte)
          (word_join (word_subword x (24*k+8, 8):byte)
            (word_subword x (24*k, 8):byte):int16):24 word):int32 =
      word_zx(word_subword x (24*k, 24):24 word)`,
  CONV_TAC WORD_BLAST);;

(* High lane (coefficients 4-7, offset by 32 bits in 128-bit source): *)
let SHUFFLE_HIGH_LANE = prove
 ((rand o concl o (EXPAND_CASES_CONV THENC NUM_REDUCE_CONV))
  `!k. k < 4 ==>
    !y:int128.
      word_join (word 0:byte)
        (word_join (word_subword y (24*k+32+16, 8):byte)
          (word_join (word_subword y (24*k+32+8, 8):byte)
            (word_subword y (24*k+32, 8):byte):int16):24 word):int32 =
      word_zx(word_subword y (24*k+32, 24):24 word)`,
  CONV_TAC WORD_BLAST);;

(* 3-byte word_join with zero high byte = word_zx of 24-bit join *)
let BYTE_JOIN_ZX = prove
 (`!b0 b1 b2:byte.
    word_join (word_join (word 0:byte) (b2:byte):int16)
              (word_join (b1:byte) (b0:byte):int16):int32 =
    word_zx(word_join (word_join (b2:byte) (b1:byte):int16) (b0:byte):24 word):int32`,
  REPEAT GEN_TAC THEN CONV_TAC WORD_BLAST);;

(* word_and with 0x7FFFFF mask on word_zx of 24-bit = word_zx of 23-bit subword *)
let BYTE_JOIN_SUBWORD_ZX = prove
 (`!b0 b1 b2:byte.
    word_and (word_zx(word_join (word_join (b2:byte) (b1:byte):int16) (b0:byte):24 word):int32)
             (word 8388607:int32) =
    word_zx(word_subword (word_join (word_join (b2:byte) (b1:byte):int16) (b0:byte):24 word) (0,23):23 word):int32`,
  REPEAT GEN_TAC THEN CONV_TAC WORD_BLAST);;

(* Little-endian 3-byte decomposition of 24-bit words *)
let LITTLE_ENDIAN_3BYTES = prove
 (`!w:24 word. val(word_subword w (0,8):byte) +
               256 * val(word_subword w (8,8):byte) +
               65536 * val(word_subword w (16,8):byte) = val w`,
  GEN_TAC THEN CONV_TAC WORD_BLAST);;

(* Little-endian 3-byte reconstruction at num level *)
let BYTES3_NUM = prove
 (`!n. n MOD 256 + 256 * (n DIV 256) MOD 256 + 65536 * (n DIV 65536) MOD 256 = n MOD 16777216`,
  GEN_TAC THEN
  SUBGOAL_THEN `16777216 = 65536 * 256` SUBST1_TAC THENL
   [ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `65536 = 256 * 256` SUBST1_TAC THENL
   [ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[GSYM DIV_DIV; MOD_MULT_MOD] THEN
  REWRITE_TAC[ARITH_RULE `256 * 256 * 256 = 256 * (256 * 256)`] THEN
  REWRITE_TAC[MOD_MULT_MOD] THEN
  MP_TAC(SPEC `256` (SPEC `n:num` DIVISION)) THEN
  MP_TAC(SPEC `256` (SPEC `n DIV 256` DIVISION)) THEN
  REWRITE_TAC[ARITH_RULE `~(256 = 0)`] THEN ARITH_TAC);;

(* val of 3-byte word_join *)
let BYTE_JOIN_VAL = prove
 (`!b0 b1 b2:byte.
    val(word_join (word_join (b2:byte) (b1:byte):int16) (b0:byte) : 24 word) =
    val b0 + 256 * val b1 + 65536 * val b2`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[VAL_WORD_JOIN; DIMINDEX_8; DIMINDEX_16] THEN
  CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN
  MP_TAC(ISPEC `b0:byte` VAL_BOUND) THEN
  MP_TAC(ISPEC `b1:byte` VAL_BOUND) THEN
  MP_TAC(ISPEC `b2:byte` VAL_BOUND) THEN
  REWRITE_TAC[DIMINDEX_8] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `256 * val(b2:byte) + val(b1:byte) < 65536`
    (fun th -> SIMP_TAC[th; MOD_LT]) THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `256 * (256 * val(b2:byte) + val(b1:byte)) + val(b0:byte) < 16777216`
    (fun th -> SIMP_TAC[th; MOD_LT]) THENL [ASM_ARITH_TAC; ARITH_TAC]);;

(* val of byte_join from word n : int256 = n DIV 2^ofs MOD 2^24 *)
let BYTE_JOIN_VAL_WORD = prove
 (`!n ofs.
    val(word_join (word_join (word_subword (word n:int256) (ofs+16,8):byte)
                             (word_subword (word n:int256) (ofs+8,8):byte):int16)
                  (word_subword (word n:int256) (ofs,8):byte) : 24 word) =
    (n MOD 2 EXP 256) DIV 2 EXP ofs MOD 2 EXP 24`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[BYTE_JOIN_VAL; VAL_WORD_SUBWORD; VAL_WORD; DIMINDEX_8] THEN
  CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[EXP_ADD; GSYM DIV_DIV] THEN CONV_TAC NUM_REDUCE_CONV THEN
  SPEC_TAC(`(n MOD 2 EXP 256) DIV 2 EXP ofs`, `m:num`) THEN
  REWRITE_TAC[BYTES3_NUM]);;

(* Full coefficient lemma: byte_join + 23-bit mask from word n = word(n DIV 2^ofs MOD 2^23) *)
let COEFF_BYTE_JOIN_WORD = prove
 (`!n ofs.
    word_zx(word_subword
      (word_join (word_join (word_subword (word n:int256) (ofs+16,8):byte)
                            (word_subword (word n:int256) (ofs+8,8):byte):int16)
                 (word_subword (word n:int256) (ofs,8):byte) : 24 word)
     (0,23) : 23 word) : int32 =
    word((n MOD 2 EXP 256) DIV 2 EXP ofs MOD 2 EXP 23)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_ZX_GEN; VAL_WORD_SUBWORD; VAL_WORD;
              DIMINDEX_8; DIMINDEX_32] THEN
  CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[BYTE_JOIN_VAL_WORD; DIV_1] THEN
  ONCE_REWRITE_TAC[GSYM(NUM_REDUCE_CONV `2 EXP 24`)] THEN
  ONCE_REWRITE_TAC[GSYM(NUM_REDUCE_CONV `2 EXP 23`)] THEN
  ONCE_REWRITE_TAC[GSYM(NUM_REDUCE_CONV `2 EXP 32`)] THEN
  REWRITE_TAC[MOD_MOD_EXP_MIN] THEN CONV_TAC NUM_REDUCE_CONV);;

(* Reduce MOD 2^256 to MOD 2^192 in DIV/MOD extraction context *)
let MOD_256_192 = prove
 (`!n k. k + 23 <= 192 ==>
    (n MOD 2 EXP 256) DIV (2 EXP k) MOD (2 EXP 23) =
    (n MOD 2 EXP 192) DIV (2 EXP k) MOD (2 EXP 23)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[DIV_MOD; GSYM EXP_ADD; MOD_MOD_EXP_MIN] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
  ASM_ARITH_TAC);;

(* word_popcount is preserved through word_zx *)
(* val(word n : 24 word) MOD 2^23 = n MOD 2^23 — avoids MOD_MOD_EXP_MIN loop *)
let VAL_WORD_24_MOD_23 = prove
 (`!n. val(word n : 24 word) MOD 2 EXP 23 = n MOD 2 EXP 23`,
  GEN_TAC THEN REWRITE_TAC[VAL_WORD] THEN
  CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN
  REWRITE_TAC[MOD_MOD_EXP_MIN] THEN
  CONV_TAC NUM_REDUCE_CONV);;

(* MAP of REJ_SAMPLE coefficient extraction = concrete list *)
let MAP_REJ_COEFFS = prove
 (`!l:(24 word)list. LENGTH l = 8 ==>
   MAP (\x:24 word. word(val x MOD 2 EXP 23):int32) l =
   [word(num_of_wordlist l MOD 2 EXP 23);
    word(num_of_wordlist l DIV 2 EXP 24 MOD 2 EXP 23);
    word(num_of_wordlist l DIV 2 EXP 48 MOD 2 EXP 23);
    word(num_of_wordlist l DIV 2 EXP 72 MOD 2 EXP 23);
    word(num_of_wordlist l DIV 2 EXP 96 MOD 2 EXP 23);
    word(num_of_wordlist l DIV 2 EXP 120 MOD 2 EXP 23);
    word(num_of_wordlist l DIV 2 EXP 144 MOD 2 EXP 23);
    word(num_of_wordlist l DIV 2 EXP 168 MOD 2 EXP 23)]`,
  GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[LIST_EQ] THEN
  CONV_TAC(ONCE_DEPTH_CONV LENGTH_CONV) THEN
  REWRITE_TAC[LENGTH_MAP] THEN ASM_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[EL_MAP; EL_NUM_OF_WORDLIST;
    ARITH_RULE `LENGTH l = 8 ==> (n < 8 ==> n < LENGTH l)`] THEN
  REWRITE_TAC[VAL_WORD_24_MOD_23] THEN
  CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN
  CONV_TAC EXPAND_CASES_CONV THEN REPEAT CONJ_TAC THEN
  CONV_TAC(ONCE_DEPTH_CONV EL_CONV) THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN
  REWRITE_TAC[DIV_1]);;

(* NOTE: REJ_SAMPLE_COEFFS was moved to the main proof file because
   it depends on REJ_SAMPLE which is defined there, not in the helpers. *)

(* SUB_LIST(0, LENGTH l) l = l — needed for BYTES_EQ_NUM_OF_WORDLIST_APPEND *)
let SUB_LIST_0_LENGTH = prove
 (`!l:(A)list. SUB_LIST(0, LENGTH l) l = l`,
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[SUB_LIST_CLAUSES; LENGTH]);;

(* Memory bytes split: read(bytes(a, m+n)) = read(bytes(a,m)) + 2^(8m) * read(bytes(a+m, n)) *)
let MEMORY_BYTES_SPLIT = prove
 (`!a m n s. read (memory :> bytes (a:int64, m + n)) s =
             read (memory :> bytes (a, m)) s +
             2 EXP (8 * m) * read (memory :> bytes (word_add a (word m), n)) s`,
  REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_COMBINE]);;

(* CMP_MASK_CORRECT: VMOVMSKPS(VPSUBD(coeffs, Q)) = bitval sum of (val c_k < Q).
   Connects the comparison mask byte to the FILTER predicate. *)
let CMP_MASK_CORRECT = prove(
 `!c0 c1 c2 c3 c4 c5 c6 c7:int32.
  val c0 < 8388608 /\ val c1 < 8388608 /\ val c2 < 8388608 /\
  val c3 < 8388608 /\ val c4 < 8388608 /\ val c5 < 8388608 /\
  val c6 < 8388608 /\ val c7 < 8388608 ==>
  val(word_zx(word_zx(word_of_bits
    (\i. i < 8 /\
     bit (32 * i + 31)
     (word_join
       (word_join
         (word_join
           (word_sub c7 (word 8380417):int32)
           (word_sub c6 (word 8380417):int32) : (64)word)
         (word_join
           (word_sub c5 (word 8380417):int32)
           (word_sub c4 (word 8380417):int32) : (64)word) : (128)word)
       (word_join
         (word_join
           (word_sub c3 (word 8380417):int32)
           (word_sub c2 (word 8380417):int32) : (64)word)
         (word_join
           (word_sub c1 (word 8380417):int32)
           (word_sub c0 (word 8380417):int32) : (64)word) : (128)word)
       :int256)) :byte) :int32) :int64) =
  bitval(val c0 < 8380417) + 2 * bitval(val c1 < 8380417) +
  4 * bitval(val c2 < 8380417) + 8 * bitval(val c3 < 8380417) +
  16 * bitval(val c4 < 8380417) + 32 * bitval(val c5 < 8380417) +
  64 * bitval(val c6 < 8380417) + 128 * bitval(val c7 < 8380417)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[VMOVMSKPS_BYTE_EQ; BIT_SUBWORD_256] THEN
  CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
  ASM_SIMP_TAC[VPSUBD_SIGN_BIT_BOUNDED; SIGN_BIT_BITVAL] THEN
  REWRITE_TAC[bitval] THEN
  REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN
  CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV) THEN
  CONV_TAC NUM_REDUCE_CONV);;

(* Pre-compute the 256 table entry values for VPERMD brute force.
   Each entry is an int64 value: 8 bytes from the table at offset 8*mask. *)
let TABLE_ENTRY_VALS =
  let table_expanded =
    (REWRITE_CONV[mldsa_rej_uniform_table; num_of_wordlist; DIMINDEX_8] THENC
     DEPTH_CONV WORD_NUM_RED_CONV THENC NUM_REDUCE_CONV)
    `num_of_wordlist mldsa_rej_uniform_table` in
  let table_num = rhs(concl table_expanded) in
  Printf.printf "  TABLE_ENTRY_VALS: computing 256 entries...\n%!";
  let entries = Array.init 256 (fun m ->
    let tm = mk_comb(mk_comb(`(MOD)`,
      mk_comb(mk_comb(`(DIV)`, table_num),
      mk_comb(mk_comb(`(EXP)`, `2`), mk_numeral(Num.num_of_int(64*m))))),
      mk_comb(mk_comb(`(EXP)`, `2`), `64`)) in
    let th = NUM_REDUCE_CONV tm in
    let rhs_val = rhs(concl th) in
    (* Prove: (num_of_wordlist table DIV 2^(64*m)) MOD 2^64 = entry_m *)
    let lhs_tm = mk_comb(mk_comb(`(MOD)`,
      mk_comb(mk_comb(`(DIV)`,
        `num_of_wordlist mldsa_rej_uniform_table`),
      mk_comb(mk_comb(`(EXP)`, `2`), mk_numeral(Num.num_of_int(64*m))))),
      mk_comb(mk_comb(`(EXP)`, `2`), `64`)) in
    let eq = mk_eq(lhs_tm, rhs_val) in
    EQT_ELIM((REWRITE_CONV[table_expanded] THENC NUM_REDUCE_CONV) eq)) in
  Printf.printf "  TABLE_ENTRY_VALS: done (%d entries)\n%!" (Array.length entries);
  entries;;

(* TABLE_ENTRY_FROM_MEMORY: connect bytes64 memory read at table+8k to
   (table_num DIV 2^(64k)) MOD 2^64 via bigdigit/bignum_from_memory *)
let TABLE_ENTRY_FROM_MEMORY = prove(
  `!table (s:x86state) k.
   read(memory :> bytes(table:int64, 2048)) s =
     num_of_wordlist(mldsa_rej_uniform_table:byte list) /\
   k < 256
   ==> val(read(memory :> bytes64(word_add table (word(8 * k)))) s :int64) =
       (num_of_wordlist mldsa_rej_uniform_table DIV 2 EXP (64 * k)) MOD 2 EXP 64`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`256`; `table:int64`; `s:x86state`; `k:num`]
    BIGDIGIT_BIGNUM_FROM_MEMORY) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[bigdigit] THEN AP_THM_TAC THEN AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN CONV_TAC NUM_REDUCE_CONV THEN
  ASM_REWRITE_TAC[]);;

(* TABLE_NUM_THM: expand mldsa_rej_uniform_table to a numeral for table lookup *)
let TABLE_NUM_THM =
  (REWRITE_CONV[mldsa_rej_uniform_table; num_of_wordlist; DIMINDEX_8] THENC
   DEPTH_CONV WORD_NUM_RED_CONV THENC NUM_REDUCE_CONV)
  `num_of_wordlist mldsa_rej_uniform_table`;;

(* VAL_WORD_GALOIS_64: derive x = word n from val x = n *)
let VAL_WORD_GALOIS_64 = prove(
  `!x:int64 n. val x = n /\ n < 18446744073709551616 ==> x = word n`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `x:int64 = word(val x)` SUBST1_TAC THENL
  [REWRITE_TAC[WORD_VAL]; ASM_REWRITE_TAC[]]);;

(* VAL_WORD_JOIN8: flatten nested val(word_join^8) to sum of 2^(32*k) * val(ck) *)
let VAL_WORD_JOIN8 = prove(
  `!(c0:int32)(c1:int32)(c2:int32)(c3:int32)(c4:int32)(c5:int32)(c6:int32)(c7:int32).
   val(word_join
     (word_join (word_join c7 c6:(64)word) (word_join c5 c4:(64)word):(128)word)
     (word_join (word_join c3 c2:(64)word) (word_join c1 c0:(64)word):(128)word)
     :int256) =
   val c0 + 2 EXP 32 * val c1 + 2 EXP 64 * val c2 + 2 EXP 96 * val c3 +
   2 EXP 128 * val c4 + 2 EXP 160 * val c5 + 2 EXP 192 * val c6 + 2 EXP 224 * val c7`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[VAL_WORD_JOIN; DIMINDEX_32; DIMINDEX_64; DIMINDEX_128] THEN
  CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN
  MAP_EVERY (fun c -> MP_TAC(ISPEC c VAL_BOUND) THEN REWRITE_TAC[DIMINDEX_32] THEN
    CONV_TAC NUM_REDUCE_CONV) [`c0:int32`;`c1:int32`;`c2:int32`;`c3:int32`;
    `c4:int32`;`c5:int32`;`c6:int32`;`c7:int32`] THEN
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `4294967296 * val(c1:int32) + val(c0:int32) < 18446744073709551616`
    (fun th -> REWRITE_TAC[MATCH_MP MOD_LT th]) THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `4294967296 * val(c3:int32) + val(c2:int32) < 18446744073709551616`
    (fun th -> REWRITE_TAC[MATCH_MP MOD_LT th]) THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `4294967296 * val(c5:int32) + val(c4:int32) < 18446744073709551616`
    (fun th -> REWRITE_TAC[MATCH_MP MOD_LT th]) THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `4294967296 * val(c7:int32) + val(c6:int32) < 18446744073709551616`
    (fun th -> REWRITE_TAC[MATCH_MP MOD_LT th]) THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `18446744073709551616 * (4294967296 * val(c3:int32) + val(c2:int32)) +
    (4294967296 * val(c1:int32) + val(c0:int32)) <
    340282366920938463463374607431768211456`
    (fun th -> REWRITE_TAC[MATCH_MP MOD_LT th]) THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `18446744073709551616 * (4294967296 * val(c7:int32) + val(c6:int32)) +
    (4294967296 * val(c5:int32) + val(c4:int32)) <
    340282366920938463463374607431768211456`
    (fun th -> REWRITE_TAC[MATCH_MP MOD_LT th]) THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `340282366920938463463374607431768211456 *
    (18446744073709551616 * (4294967296 * val(c7:int32) + val(c6:int32)) +
     (4294967296 * val(c5:int32) + val(c4:int32))) +
    (18446744073709551616 * (4294967296 * val(c3:int32) + val(c2:int32)) +
     (4294967296 * val(c1:int32) + val(c0:int32))) <
    115792089237316195423570985008687907853269984665640564039457584007913129639936`
    (fun th -> REWRITE_TAC[MATCH_MP MOD_LT th]) THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  ARITH_TAC);;

(* MOD_BASE_REWRITES: convert numeral MOD bases to symbolic 2 EXP k *)
let MOD_BASE_REWRITES = [
  GSYM(NUM_REDUCE_CONV `2 EXP 32`);
  GSYM(NUM_REDUCE_CONV `2 EXP 64`);
  GSYM(NUM_REDUCE_CONV `2 EXP 96`);
  GSYM(NUM_REDUCE_CONV `2 EXP 128`);
  GSYM(NUM_REDUCE_CONV `2 EXP 160`);
  GSYM(NUM_REDUCE_CONV `2 EXP 192`);
  GSYM(NUM_REDUCE_CONV `2 EXP 224`);
  GSYM(NUM_REDUCE_CONV `2 EXP 256`)];;

(* VAL_BOUND_256: val(x:int256) < 2 EXP 256 *)
let VAL_BOUND_256 = prove(
  `!x:int256. val x < 2 EXP 256`,
  GEN_TAC THEN MP_TAC(ISPEC `x:int256` VAL_BOUND) THEN
  REWRITE_TAC[DIMINDEX_256]);;

(* Factor rules for MOD stripping: rewrite 2^k * x to (2^(k-m) * x) * 2^m *)
let vpermd_factor_for m = List.filter_map (fun k ->
  if k >= m && k <= 224 then
    Some(ARITH_RULE(mk_eq(
      mk_comb(mk_comb(`(*)`, mk_comb(mk_comb(`EXP`,`2`),mk_numeral(Num.num_of_int k))), `x:num`),
      mk_comb(mk_comb(`(*)`, mk_comb(mk_comb(`(*)`,
        mk_comb(mk_comb(`EXP`,`2`),mk_numeral(Num.num_of_int(k-m)))), `x:num`)),
        mk_comb(mk_comb(`EXP`,`2`),mk_numeral(Num.num_of_int m))))))
  else None)
  [32;64;96;128;160;192;224];;

let VPERMD_FACTOR_RULES = List.map (fun m -> (m, vpermd_factor_for m))
  [32;64;96;128;160;192;224];;

(* VPERMD_FACTOR_STRIP_TAC: detect MOD base, apply factor rules, strip, MOD_LT *)
let VPERMD_FACTOR_STRIP_TAC : tactic = fun (asl, w) ->
  let base = try
    let mod_term = rand(lhand w) in
    Num.int_of_num(dest_numeral(rand mod_term))
  with _ -> 0 in
  let gk = try List.assoc base VPERMD_FACTOR_RULES with Not_found -> [] in
  (if gk = [] then ALL_TAC
   else
     REWRITE_TAC gk THEN
     TRY(ONCE_REWRITE_TAC[ARITH_RULE `a+b+c+d+e+f+g+h = (a+b+c+d+e+f+g)+h`] THEN REWRITE_TAC[MOD_MULT_ADD]) THEN
     TRY(ONCE_REWRITE_TAC[ARITH_RULE `a+b+c+d+e+f+g = (a+b+c+d+e+f)+g`] THEN REWRITE_TAC[MOD_MULT_ADD]) THEN
     TRY(ONCE_REWRITE_TAC[ARITH_RULE `a+b+c+d+e+f = (a+b+c+d+e)+f`] THEN REWRITE_TAC[MOD_MULT_ADD]) THEN
     TRY(ONCE_REWRITE_TAC[ARITH_RULE `a+b+c+d+e = (a+b+c+d)+e`] THEN REWRITE_TAC[MOD_MULT_ADD]) THEN
     TRY(ONCE_REWRITE_TAC[ARITH_RULE `a+b+c+d = (a+b+c)+d`] THEN REWRITE_TAC[MOD_MULT_ADD]) THEN
     TRY(ONCE_REWRITE_TAC[ARITH_RULE `a+b+c = (a+b)+c`] THEN REWRITE_TAC[MOD_MULT_ADD]) THEN
     TRY(REWRITE_TAC[MOD_MULT_ADD]) THEN
     TRY(MATCH_MP_TAC MOD_LT THEN
         REWRITE_TAC[MULT_CLAUSES] THEN
         RULE_ASSUM_TAC(REWRITE_RULE[DIMINDEX_32]) THEN ASM_ARITH_TAC))
  (asl, w);;

(* VPERMD_TABLE_CORRECT: 256-case brute force proof that VPERMD with the mldsa
   table correctly compacts coefficients matching FILTER.
   Preconditions: 8 coefficients bounded < 2^23, table entry for the mask.
   Conclusion: val(VPERMD result) MOD 2^(32*popcount) = num_of_wordlist(FILTER ...) *)
let VPERMD_TABLE_CORRECT = time prove(
  `!(c0:int32) (c1:int32) (c2:int32) (c3:int32) (c4:int32) (c5:int32) (c6:int32) (c7:int32) (te:int64).
   val c0 < 8388608 /\ val c1 < 8388608 /\ val c2 < 8388608 /\ val c3 < 8388608 /\
   val c4 < 8388608 /\ val c5 < 8388608 /\ val c6 < 8388608 /\ val c7 < 8388608 /\
   val te = (num_of_wordlist mldsa_rej_uniform_table DIV
     2 EXP (64 * (bitval(val c0 < 8380417) + 2 * bitval(val c1 < 8380417) +
     4 * bitval(val c2 < 8380417) + 8 * bitval(val c3 < 8380417) +
     16 * bitval(val c4 < 8380417) + 32 * bitval(val c5 < 8380417) +
     64 * bitval(val c6 < 8380417) + 128 * bitval(val c7 < 8380417))))
     MOD 2 EXP 64
   ==>
   let coeffs = word_join
     (word_join (word_join c7 c6 :(64)word) (word_join c5 c4 :(64)word) :(128)word)
     (word_join (word_join c3 c2 :(64)word) (word_join c1 c0 :(64)word) :(128)word) :int256 in
   let ix = word_join
     (word_join (word_join (word_zx(word_subword te (56,8):byte):int32)
                           (word_zx(word_subword te (48,8):byte):int32) :(64)word)
               (word_join (word_zx(word_subword te (40,8):byte):int32)
                          (word_zx(word_subword te (32,8):byte):int32) :(64)word) :(128)word)
     (word_join (word_join (word_zx(word_subword te (24,8):byte):int32)
                           (word_zx(word_subword te (16,8):byte):int32) :(64)word)
               (word_join (word_zx(word_subword te (8,8):byte):int32)
                          (word_zx(word_subword te (0,8):byte):int32) :(64)word) :(128)word) :int256 in
   let res = word_join
     (word_join (word_join (word_subword coeffs (32 * val(word_subword ix (224,3):(3)word), 32) :int32)
                           (word_subword coeffs (32 * val(word_subword ix (192,3):(3)word), 32) :int32) :(64)word)
               (word_join (word_subword coeffs (32 * val(word_subword ix (160,3):(3)word), 32) :int32)
                          (word_subword coeffs (32 * val(word_subword ix (128,3):(3)word), 32) :int32) :(64)word) :(128)word)
     (word_join (word_join (word_subword coeffs (32 * val(word_subword ix (96,3):(3)word), 32) :int32)
                           (word_subword coeffs (32 * val(word_subword ix (64,3):(3)word), 32) :int32) :(64)word)
               (word_join (word_subword coeffs (32 * val(word_subword ix (32,3):(3)word), 32) :int32)
                          (word_subword coeffs (32 * val(word_subword ix (0,3):(3)word), 32) :int32) :(64)word) :(128)word) :int256 in
   val res MOD 2 EXP (32 * (bitval(val c0 < 8380417) + bitval(val c1 < 8380417) +
     bitval(val c2 < 8380417) + bitval(val c3 < 8380417) +
     bitval(val c4 < 8380417) + bitval(val c5 < 8380417) +
     bitval(val c6 < 8380417) + bitval(val c7 < 8380417))) =
   num_of_wordlist(FILTER (\c:int32. val c < 8380417) [c0;c1;c2;c3;c4;c5;c6;c7])`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  FIRST_X_ASSUM MP_TAC THEN
  MAP_EVERY ASM_CASES_TAC
    [`val(c0:int32) < 8380417`; `val(c1:int32) < 8380417`;
     `val(c2:int32) < 8380417`; `val(c3:int32) < 8380417`;
     `val(c4:int32) < 8380417`; `val(c5:int32) < 8380417`;
     `val(c6:int32) < 8380417`; `val(c7:int32) < 8380417`] THEN
  ASM_REWRITE_TAC[bitval] THEN
  CONV_TAC(LAND_CONV(RAND_CONV(REWRITE_CONV[TABLE_NUM_THM] THENC NUM_REDUCE_CONV))) THEN
  DISCH_THEN(fun th ->
    let n = rhs(concl th) in
    SUBST_ALL_TAC(MATCH_MP VAL_WORD_GALOIS_64
      (CONJ th (EQT_ELIM(NUM_REDUCE_CONV(mk_comb(mk_comb(`(<)`,n), `18446744073709551616`))))))) THEN
  CONV_TAC(DEPTH_CONV(WORD_NUM_RED_CONV ORELSEC WORD_SIMPLE_SUBWORD_CONV)) THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[FILTER] THEN ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN
  TRY(REWRITE_TAC[MOD_1; num_of_wordlist] THEN REFL_TAC) THEN
  REWRITE_TAC MOD_BASE_REWRITES THEN
  TRY(SIMP_TAC[MOD_LT; VAL_BOUND_256]) THEN
  REWRITE_TAC[VAL_WORD_JOIN8] THEN
  CONV_TAC(RAND_CONV(REWRITE_CONV[num_of_wordlist; ADD_0; DIMINDEX_32;
    LEFT_ADD_DISTRIB; MULT_CLAUSES; MULT_ASSOC; GSYM(SPEC `2` EXP_ADD)] THENC
    DEPTH_CONV NUM_ADD_CONV)) THEN
  TRY REFL_TAC THEN
  VPERMD_FACTOR_STRIP_TAC);;

(* RESOLVE_TABLE_READ_TAC: resolve read(bytes64(word_add table (word K))) terms
   in the goal using TABLE_ENTRY_FROM_MEMORY + the memory-table hypothesis *)
let RESOLVE_TABLE_READ_TAC : tactic = fun (asl,w) ->
  let mem_hyps = List.filter_map (fun (_,th) ->
    if is_eq(concl th) &&
       (try let c = string_of_term(concl th) in
        let _ = String.index c '2' in
        String.length c > 60 &&
        can (find_term (fun t -> try fst(dest_const t) = "num_of_wordlist" with _ -> false)) (concl th) &&
        can (find_term (fun t -> try dest_numeral t = Num.num_of_int 2048 with _ -> false)) (concl th)
        with _ -> false)
    then Some th else None) asl in
  if mem_hyps = [] then ALL_TAC (asl,w) else
  let reads = find_terms (fun t ->
    try let _ = find_term (fun s -> try fst(dest_const s) = "bytes64" with _ -> false) t in
        let _ = find_term (fun s -> try fst(dest_const s) = "word_add" with _ -> false) t in
        fst(dest_const(fst(strip_comb t))) = "read" &&
        is_comb t && is_var(rand t)
    with _ -> false) w in
  let eqs = List.filter_map (fun rd ->
    try
      let state = rand rd in
      (* rd = read (memory :> bytes64(word_add table (word K))) sNN
         rator rd = read (memory :> bytes64(word_add table (word K)))
         rand(rator rd) = memory :> bytes64(word_add table (word K))
         rand(rand(rator rd)) = bytes64(word_add table (word K))
         rand(rand(rand(rator rd))) = word_add table (word K) *)
      let word_add_tm = rand(rand(rand(rator rd))) in
      let k_tm = rand(rand word_add_tm) in  (* K : num *)
      let k = Num.int_of_num(dest_numeral k_tm) in
      let mask = k / 8 in
      let table_var = rand(rator word_add_tm) in
      (* Find memory hypothesis for this state *)
      let mem_th = try List.find (fun th ->
        try rand(rator(lhs(concl th))) = state with _ -> false) mem_hyps
        with Not_found -> List.hd mem_hyps in
      let spec = SPECL [table_var; state; mk_numeral(Num.num_of_int mask)]
        TABLE_ENTRY_FROM_MEMORY in
      let prem_th = CONJ mem_th
        (EQT_ELIM(NUM_REDUCE_CONV(mk_comb(mk_comb(`(<)`,mk_numeral(Num.num_of_int mask)), `256`)))) in
      let val_eq = MP spec prem_th in
      let val_eq' = CONV_RULE(RAND_CONV(REWRITE_CONV[TABLE_NUM_THM] THENC NUM_REDUCE_CONV)) val_eq in
      (* Also reduce 8*mask in the LHS to match the goal's concrete address *)
      let val_eq'' = CONV_RULE(LAND_CONV(DEPTH_CONV NUM_REDUCE_CONV)) val_eq' in
      let n = rhs(concl val_eq'') in
      Some(MATCH_MP VAL_WORD_GALOIS_64
        (CONJ val_eq'' (EQT_ELIM(NUM_REDUCE_CONV
          (mk_comb(mk_comb(`(<)`,n), `18446744073709551616`))))))
    with _ -> None) reads in
  if eqs = [] then ALL_TAC (asl,w)
  else REWRITE_TAC eqs (asl,w);;

(* VPERMD_MEMORY_BRIDGE: connect a sub-read of the 32-byte VMOVDQU write
   region to the VPERMD MOD result, closing the memory store goal. *)
let VPERMD_MEMORY_BRIDGE = prove
 (`!a (s:x86state) vr n l.
    read(memory :> bytes(a:int64, 32)) s = vr /\
    vr MOD 2 EXP (32 * n) = num_of_wordlist(l:int32 list) /\
    n <= 8
    ==> read(memory :> bytes(a, 4 * n)) s = num_of_wordlist l`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
    `read(memory :> bytes(a:int64, 4 * n)) s =
     read(memory :> bytes(a, 32)) s MOD 2 EXP (8 * (4 * n))`
  SUBST1_TAC THENL
   [REWRITE_TAC[READ_COMPONENT_COMPOSE; GSYM READ_BYTES_MOD] THEN
    GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV)
      [GSYM(NUM_REDUCE_CONV `8 * 32`)] THEN
    REWRITE_TAC[READ_BYTES_MOD] THEN
    SUBGOAL_THEN `MIN 32 (4 * n) = 4 * n` SUBST1_TAC THENL
     [REWRITE_TAC[MIN] THEN ASM_ARITH_TAC;
      REFL_TAC];
    ASM_REWRITE_TAC[ARITH_RULE `8 * 4 * n = 32 * n`]]);;

(* VAL_READ_BYTES256: val(read(bytes256 addr) s) = read(bytes(addr,32)) s
   Converts a 256-bit word read to a numeric bytes read. *)
let VAL_READ_BYTES256 = prove(
  `!addr (s:(int64->byte)).
    val(read(bytes256 addr) s :int256) = read(bytes(addr,32)) s`,
  REWRITE_TAC[BYTES256_WBYTES; VAL_READ_WBYTES; DIMINDEX_256] THEN
  CONV_TAC NUM_REDUCE_CONV);;
