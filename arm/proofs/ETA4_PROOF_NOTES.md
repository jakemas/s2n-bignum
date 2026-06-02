# ML-DSA rej_uniform_eta4 Proof Notes

Status: WIP with 4 CHEATs, proof structure validated end-to-end.

## Proof Architecture

1. **ENSURES_SEQUENCE_TAC** at pc+256: splits into computation + writeback
2. **WOP-based loop count**: `?N. buflen<8*(N+1) \/ 256<=LENGTH(REJ_NIBBLES(...))` + minimality
3. **ENSURES_WHILE_UP_TAC** with `N` iterations
4. **Loop body split** at pc+0xe0 (SIMD compute vs ST stores)
5. **Post-loop case analysis**: 256<=niblen (enough samples) vs buffer exhausted

## Remaining CHEATs (4)

### CHEAT #1 (line 720): Writeback memory content
Goal: `read(memory :> bytes(res, 4*MIN 256 niblen)) s245 = num_of_wordlist(SUB_LIST(0, MIN 256 niblen)(MAP word_sx niblist))`

**Approach**: 
- Use `BYTES_EQ_NUM_OF_WORDLIST_APPEND` pattern from PR #378
- BIGNUM_LDIGITIZE stack memory, MEMORY_128_FROM_64 conversion
- Per-iteration WB_BLOCK_LO/HI identities (already in proof file)
- SSHLL + SUB simplification via BITBLAST

### CHEAT #2 (line 919): Counting bridge
Goal at CHEAT point (confirmed via interactive replay 2026-05-02):
```
bitval(val(word_subword nibbles0 (0,16)) < 9) + ... + 
bitval(val(word_subword nibbles1b (112,16)) < 9) = 
LENGTH(REJ_NIBBLES_ETA4(SUB_LIST(8*i,8) inlist))
```

**Completed helper lemmas** (in proof file, lines 454-511):
- `BYTE_AND_15_MOD`: val(word_and b 15) = val b MOD 16
- `BYTE_USHR4_DIV`: val(word_ushr b 4) = val b DIV 16
- `VAL_WORD_ZX_BYTE16`: val(word_zx b:int16) = val b
- `BYTE_NIBBLE_COUNT_EQ`: per-byte bridge
- **`COUNT_BRIDGE_ABSTRACT`**: given 16 halfword = byte-nibble identities on abstract x0, x1, the 16-bitval sum = LENGTH(REJ_NIBBLES_ETA4 [b0;...;b7])

**Remaining work**: Show `nibbles0` (= `read Q16 s11`) and `nibbles1b` (= `read Q17 s11`) have halfwords matching the byte-nibble pattern for bytes in `SUB_LIST(8*i,8) inlist`. This requires:
1. Unfolding the ABBREV hyps `read Q16/Q17 s11 = nibbles0/nibbles1b` to recover ARM semantic form
2. USHLL(ZIP1/2(AND d mask, USHR d 4)) halfword k = word_zx of appropriate byte nibble of d
3. Connect d (= `read D0 s2`, from LDR) to `word(num_of_wordlist(SUB_LIST(8i,8) inlist))` via bytes-loaded

### CHEAT #3 (line 901): Memory APPEND
Goal: `read(memory :> bytes(stackpointer, 2*(curlen+len0+len1))) s6 = num_of_wordlist(APPEND curlist newbatch)`

**Approach**:
- `BYTES_EQ_NUM_OF_WORDLIST_APPEND` to split into curlist + newbatch
- For newbatch: need Q16/Q17 values = word(num_of_wordlist of lo/hi half of newbatch)
- TBL correctness via brute force (256-entry table, heavy)
- OR: carry Q16/Q17 structure through intermediate postcondition

### CHEAT #4 (line 938): Post-loop 256<=niblen AND 8<=X2
Goal: ARM_STEPS_TAC on 4 instructions (CMP+BCS+CMP+BCS)

**Framework limit**: ARM_STEPS_TAC stack overflow with deeply nested niblen term.

**Approach**: Use ENSURES_SEQUENCE_TAC at pc+108 to split into two 2-step sequences:
```
ENSURES_SEQUENCE_TAC `pc + 108` <intermediate> THEN
CONJ_TAC THENL [ARM_STEPS (1--2); 
                SUBGOAL_THEN 256<=val(word niblen) + ARM_STEPS (1--2)]
```

## Key Lemmas Available

- `REJ_NIBBLES_ETA4`, `REJ_NIBBLES_ETA4_APPEND`, `REJ_NIBBLES_ETA4_STEP`
- `REJ_NIBBLES_COUNT_8`: 8-byte count = 16-bitval sum
- `NIBLEN_BOUND_FROM_WOP`: niblen < 272 from WOP
- `UADDLV_BOUND_LEMMA`, `UADDLV_COUNT_LEMMA`: 8 bitvals → sum
- `POPCOUNT_AND_POWERS`: 8 BITBLAST lemmas for single-bit popcounts
- `WORD_INSERT_Q31`: Q31 initialization value
- `WORD_ADD_SHL1`: X7 pointer arithmetic
- `USHLL_HALFWORDS`: USHLL halfword = word_zx(byte)
- `WB_BLOCK_LO/HI`: writeback per-iteration
- `WORD_SX_SUB4_SMALL`: word_sx(word_sub 4 x) simplification

## Ideas for Counting Bridge

### Option A: Per-byte brute force
For each byte b, prove:
```
halfword_0_of_nibbles0(d contains b as byte 0) = val b MOD 16
halfword_1_of_nibbles0(...) = val b DIV 16
```
via WORD_BLAST per-case. Then apply REJ_NIBBLES_COUNT_8.

### Option B: Expand via EXPAND_TAC "nibbles0"
Fully expand nibbles0 ABBREV back to its ARM state definition. Each halfword becomes an explicit word_zx(word_subword d (...)) expression. Use 16-element WORD_BLAST to verify the full identity.

### Option C: Add Q16/Q17 content to intermediate postcondition
Instead of carrying just counts, carry the FULL Q16/Q17 values expressed as specific symbolic forms. Then memory/counting can both use these.

## Build Instructions

```bash
cd /home/ubuntu/apr17/s2n-bignum
cc -c -o arm/mldsa/mldsa_rej_uniform_eta4.o arm/mldsa/mldsa_rej_uniform_eta4.S
# Load proof file via HOL Light (takes ~60s for 75+35 ARM steps with CHEATs)
```

## Reference Proof (PR #378)

Full MLDSA rej_uniform proof at `/tmp/eta4/mldsa_rej_uniform_proof_ref.ml` (1728 lines).
Differences from eta4:
- eta4 uses int16 nibbles vs int32 coefficients  
- eta4 table has 256 entries (vs 16), indexed by 8-bit mask
- eta4 filter `val x < 9` vs `val x < 8380417`
