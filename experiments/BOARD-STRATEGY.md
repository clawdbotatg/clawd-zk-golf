# zk.golf full-board strategy (2026-08-06)

Synthesis of three parallel recon audits (fixed-base, sha256-hash, rsa) plus
our earlier deep audits (keccak, k12, secp variable-base). Recon details:
agents' full reports summarized here; frontier snapshots in `study/`.

## What we're actually up against

rot256 runs an automated optimize→prove→verify loop ("Aristotle" = Harmonic's
math AI) with hours-level response time, 3-4 record cuts per day across
multiple challenges simultaneously, and **ships machine-checked floor/
impossibility libraries inside the submissions** (sha256: RowAlgebra/Packing
proofs; rsa: Optimality.lean/CarryFloor.lean). This is machine-vs-machine.
Beating them = finding seams their roadmap doesn't cover, not out-grinding.

## Board state and beatability

| challenge | record | state | our assessment |
|---|---|---|---|
| assert-bytes | 240 (we tie) | done | optimal-ish |
| sha256-hash | 145470 | hot, fortified | nibbles −1..−40; seam: block-5 sparsity + deferred reduction across digest mux (NOT covered by their impossibility lib) |
| keccak-f1600 | 184320 | frozen | our proven bit-paradigm floor |
| **rsa-4096** | **321769** | 1 day old | **best target: their own CarryFloor proves 1591/step floor vs 2267/step actual = 10.1k admitted gap; windowed q·n convolution (est 4-6k) is NOT on their stated roadmap** |
| secp var-base | 316436 | active | step locally optimal (our audit); watch |
| secp fixed-base | 50395 | harvested 3-4×/day | structural only: deferred λ-normalization (~0.5-2.5k), select/fold carry fusion (~0.4-1k) |
| gf2-sha256 | 44430 | unaudited | next audit |
| gf2-blake3 | 20596 | unaudited | next audit |
| gf2-k12 | 38400=par | frozen | our proven local floor |

## Cross-cutting discovery: the range-check economy

70-80% of EVERY big-field record is range checking at exactly **2 score per
certified bit** (n−1 bits witnessed + implied top bit). RSA: 80.3% (their own
audit). Fixed-base: ~70%. secp: ~60%. The degree-doubling variety argument
makes ~2/bit look like a real floor for isolated values, and packing k values
into one wide check saves nothing. **Any structural idea on amortized bit
certification breaks the entire board at once** — this is the deep research
bet, prior art to sweep: batch range proofs without lookups, algebraic
membership certificates.

Validated cross-challenge pattern (three independent confirmations):
**reduce-once vs defer is decided by consumer count** — fixed-base defers y
through the whole comb chain (single consumer per step), variable-base
reduces y₄ every step (two consumers), sha256 defers carries into affine
chains (zero carry allocs). Any gadget with a single downstream consumer of
a reducible value is a deferral candidate.

## The program

1. **Offensive: RSA carry/window attack** (best proven gap on the board).
   a. Reproduce their cost model for the grouped-carry chain (G=39, widths
      28-32); formulate grouping as discrete optimization; search (ILP/DP)
      toward their proven 1591 floor. Gap ≈ 676/step × 15 + final-step 5504.
   b. Windowed q·n: port their WindowSquare Lo/Hi split (682→186 rows for
      the square) to the general bilinear q·n product, ~38 window points.
      Novel — not in their notes.
   c. Also audit: final step in 24-bit limbs (their 16-bit choice has a
      stated reason to check), first-squaring premium ("not shown
      unavoidable" — their words).
2. **Tooling ("our Aristotle")**: extend `gadget_synth.py` to multi-row /
   multi-output identities and carry-group optimization; wire a fast
   modify→`lake build`→cost-check rep loop on the RSA codebase.
3. **Audit the two GF(2) records** (sha256-gf2, blake3-gf2) — identity-C
   AND-count games where our K12 rank-experiment machinery applies directly.
4. **Deep bet, background**: literature sweep on sub-2/bit certification.
5. **Watcher stays live** for new challenges (still the cheapest crown).

## Sociology note

Records move −1/−7/−128 daily; a submission race with an hours-latency
automated defender means: never announce a seam by submitting a partial win
if the full win is within reach — bank the whole delta in one submission.
