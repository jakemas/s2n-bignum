# Current Cheat Status

**Live cheats: 1** (down from 8 at session start, 87.5% reduction)

## Eliminated Cheats

1. ✅ VPERMD SIMD block (formerly 256-case brute force) — now uses MLDSA_VPERMD_BRIDGE
2. ✅ Continue branch (loop body preservation i → i+1)
3. ✅ J2 count-exit branch (`248 < LENGTH(REJ_SAMPLE(SUB_LIST(0, 8*N)))`)
4. ✅ J1-A offset-exit, count also fires (outlen ≥ 256 in J1)
5. ✅ J1-B offset-exit, count doesn't fire (VSTEPS 38-39 proof)
6. ✅ Post-loop case A (outlen = 256, JAE at pc+186 fires to vzeroupper)
7. ✅ Post-loop case B1 (outlen < 256, resolve RIP s41 = pc+188, RIP s43 = pc+196)
8. Defensive CHEAT_TACs (ORELSE-guarded) throughout — all removed

## Remaining Cheat: Scalar Rejection Loop (pc+196 .. pc+242)

**Location**: `mldsa_rej_uniform.ml:1913` — inside case B of post-loop, after proving RIP s43 = pc+196.

**What's needed**: Rejection sampling loop body proof (up to 8 iterations).

**Approach** (sketched, not yet implemented):
- Use `num_WOP` to characterize K (number of scalar iterations)
- K = smallest j such that `LENGTH(REJ_SAMPLE(SUB_LIST(0, 8*N + j))) >= 256 \/ 837 < 24*N + 3*j`
- Apply `ENSURES_WHILE_UP2_TAC K (pc+181) (pc+242) invariant`
- Invariant after i iterations: RAX=outlen_i, RCX=word(24*N+3*i), memory[res,4*outlen_i]=outlist_i
- Body proof requires resolving 3 conditional branches per iteration via `RESOLVE_JA_ONLY_TAC` pattern:
  1. CMP eax 256; JAE vzeroupper (pc+181..186) — fall-through when outlen_i < 256
  2. CMP ecx 837; JA vzeroupper (pc+188..194) — fall-through when 24*N+3*i ≤ 837
  3. CMP r8d 8380417; JAE loopback (pc+224..231) — this is the REJECT branch,
     case-split on whether 24-bit coeff < Q or not
- Last iteration (i=K-1) exits to pc+242 via either count-exit or offset-exit.

**Helper lemmas already proved in defs_extra.ml**:
- `REJ_SAMPLE_SPLIT`: REJ_SAMPLE l = APPEND prefix suffix
- `REJ_SAMPLE_PREFIX_256`: LENGTH(REJ_SAMPLE prefix) = 256 ⟹ SUB_LIST(0,256) = REJ_SAMPLE prefix
- `REJ_SAMPLE_SUBLIST_256_BOUNDED`: 256 ≤ LENGTH ⟹ SUB_LIST(0,256) unchanged by suffix

**Design note**: `scalar_loop_design.ml` already identifies that the scalar loop runs at most 8 iterations (either 8 coefficients remain in input, or outlen needs ≤ 8 more to reach 256).
