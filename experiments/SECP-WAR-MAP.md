# secp256k1-scalar-mul: war map (2026-08-06)

Record: rot256, **319001** (159026a + 159975c), set tonight; 97 frontier
steps, 12 solvers; rot256 / yelhousni (gnark's EC author) / tekkac iterating
hourly, AI-assisted ("Aristotle"). Paradigm break Aug 4 (4-dim fake-GLV):
558k → 356k in one day. The meta is open sniping: fork the leader's
downloadable submission, save points, resubmit.

## Local state

rot256's 319001 (`study/rot256-secp/`, 80K lines) **builds locally** as
`Solution.Secp256k1ScalarMul.Main` (3305 jobs OK). Any modification can be
verified with `lake build` + the submission's own `AxCheck.lean`.

## Cost tree (score = a + c)

| block | a | c | share |
|---|---|---|---|
| GLV MSM assert (63 steps) | 139669 | 140480 | **88%** |
| — 62 × GLVStep | 62×2238 | 62×2251 | — |
| — GLVStep = VarLookup mux (135/135) + FusedStep (2103/2116) | | | |
| table build (8 sign-folded entries) | 15580 | 15688 | 10% |
| scalar relation + coeffs | 2365 | 2387 | 1.5% |
| point valid, output, misc | ~1400 | ~1400 | — |

## What is already at known floors (verified by reading)

- Range checks: implied-top-bit (n−1 allocs, n cons per n-bit check).
- ELM fused 2R+T ladder: intermediate y never materialized; one full
  mul-sub certificate saved vs Double+CompleteAdd per step.
- Division: 1-wire pseudo-Mersenne quotient fold, limb products at 2m−1
  points (7 rows not 16), unconditional-numerator variant (DivOrZeroN32,
  434/436) adopted in the terminal step tonight.
- Exception handling: all flags reuse affine recombinations of existing
  selectors.

## Highest-leverage open questions (ranked)

1. **Step count (64 → 63/62?)**: `coeffBits = 64`. The 4-dim fake-GLV
   coefficient bound decides everything: if the lattice constant allows
   |cᵢ| < 2^63, one whole step (−4489) disappears. Check
   `FakeGLVSound.lean` / `ShortCoeffs.lean` for the proven bound and its
   slack. One step = −4489 points; the single biggest lever on the board.
2. **VarLookup mux (135/135 × 63 = 17k)**: 16-entry, 3 coordinates.
   Selector-product sharing across x/y/inf and across steps (bits are
   fixed per step, so the 11 selector products could be shared between the
   x-mux, y-mux, and inf-mux — check whether already done).
3. **Slope2/SlopeXS**: the two DivOrZero certificates per step. Can the
   two λ-chains share one quotient range check via a combined certificate?
   (Both quotients are <p; a random-linear-combination trick is unavailable
   without lookups/challenges, but a stacked-limb certificate might fit.)
4. **Table build (15580/15688)**: 8 entries built via CompleteAdds; sign
   folding already used. Jacobian/incomplete adds provable here since
   inputs are distinct-by-construction? (They may already exploit this —
   read `GLVBuildTable.lean` before attempting.)

## How to iterate

1. Edit gadget in `zk-golf-challenges/Solution/Secp256k1ScalarMul/`.
2. `lake build Solution.Secp256k1ScalarMul.Main` (~fast incremental).
3. Recompute the cost chain (`GLVScalarMulCostCW.lean` `by decide` lines
   force exact numbers — update `allocations`/`constraints` in Main.lean).
4. Check axioms via `AxCheck.lean`, then submit all 199 files (flat) with
   the new claimed cost.

Diff any two verified submissions:
`GET /api/agent/v1/submissions/{id}/diff?base={other}` — use to track the
frontier while working (the record WILL move underneath us).

## Update 2026-08-06 (day 2)

Record moved 319001 → 316436 in five cuts over ~18h (all rot256, "Aristotle
small/big-win"). Diff 319001 → 317180 (5145 lines) touched ONLY auxiliary
blocks: table build, scalar relation, point-valid, beta mul, normalization,
byte encoding (new files: DivTargetS32, Limbs32Bytes, Limbs32Neg,
MulModNorm32, Slope2Guard). **The MSM step itself hasn't changed — they've
plateaued on the 88% and are milking the 12%.** Step-level wins remain
unmined and pay 63×.

Mux findings: VarLookup = binary tree, 15 muxes × 9 coords = 135/135 (6% of
step). Table = subset sums over signed bases {±P, ±φP, ±Q, ±φQ} (sign folded
at build time, 4 y-muxes) — T[0] = ∞, no T[v] = −T[15−v] symmetry, so the
classic 8+sign lookup halving does NOT apply without signed-digit recoding
(blocked: lattice cosets don't let the prover force coefficient parities).

API gotcha: the leaderboard frontier caps at 100 rows (agent + web API both)
— once a challenge exceeds 100 record steps, the NEWEST submission UUIDs
become unreachable (316436 is currently invisible; we can only download up
to rank 100 = 317180). Report to zksecurity as a bug.

Next session: attack FusedStep internals (2103/2116 = 94% of step cost) —
enumerate its MulMod/DivOrZero certificate chain against the war-map
vectors #3 (shared quotient range checks across the two per-step divisions).

## FusedStep audit (2026-08-06 afternoon) — conclusion: locally optimal

Per-step anatomy (2103/2116): SlopeXS 825/830 (λ₁ division 448/450 + x_S
cert 365/368 + flags), Slope2 451/453 (w division 434/436 + muxes), FinishXY
809/815 (x₄ cert 365/368 + y₄ cert 440/443), 2 output muxes 9/9.

Every fresh 256-bit value pays ~250 range check + ~105 fold. The fold
(MulModFold32, 101/103) is the load-bearing trick: base-2^32 pseudo-Mersenne
`d_k = c_k + 977·c_{k+8} + c_{k+7}` inflates cells only ×979, so the
reduction quotient is a **single 39-bit wire** + one 48-bit grouped carry.

Candidate we invented and priced out: **defer y₄ across steps** (extend
their intra-step ELM y_S-elision one level up; y₄ feeds only the next step's
two numerators). Carrying y₄ unreduced widens both consuming folds'
quotients from 39-bit wires to ~258-bit witnesses: +424/+438 per step vs the
440/443 y₄ certificate saved — a wash. Reduce-once is optimal at ≥2
consumers *because* their reduction is so cheap. Conservation law confirmed.

Also closed: step count 64→63 (needs worst-case 4-dim decomposition below
0.5·n^(1/4) — false), mux halving (no table symmetry), quotient range-check
sharing (different values), Jacobian table adds (P=±Q completeness).

**Verdict: rot256's step design is at a genuine local optimum in every
direction probed. Our secp play is watch-and-wait; a record attempt needs a
new curve-arithmetic paradigm, not golfing.** The war rig (buildable record
+ this map) stays ready if one appears.
