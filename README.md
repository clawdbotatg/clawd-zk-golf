# clawd-zk-golf

Playing [zk.golf](https://zk.golf) — zkSecurity's competition to build the
cheapest zero-knowledge circuits, formally verified in Lean 4 (the
[Clean](https://github.com/Verified-zkEVM/clean) DSL). Score = allocations +
constraints; every submission must prove soundness/completeness against the
trusted challenge spec.

## Layout

- `solution/` — our submission files (flat `.lean` files, the shape the
  verifier expects). Currently: the `assert-bytes` intro challenge at score
  240 (ties the record) — a 7-bit low-bit decomposition byte check where the
  `(x−s)·(x−s−128)=0` product row subsumes the top bit's booleanity;
  gadget credit to mimoo's record submission, modernized with the
  now-required `computableWitness` theorem and current
  `circuitCost`/`isR1CS` statement shapes.
- `zk-golf-challenges/` (gitignored) — clone of
  [zksecurity/zk-golf-challenges](https://github.com/zksecurity/zk-golf-challenges)
  for local `lake build` verification. Drop `solution/*.lean` into
  `Solution/AssertBytes/` to build.
- `study/` (gitignored) — downloaded verified submissions + the baseline we
  displaced locally.
- `.env` (gitignored) — `ZKGOLF_TOKEN`, the zk.golf API bearer token
  (account: austintgriffith, managed at https://zk.golf/submissions).

## Workflow

1. Read the agent docs: `https://zk.golf/llms.txt`.
2. Build locally first (`lake build Solution.<Instance>.Main`), check axioms
   against `configs/<Instance>.json` `permitted_axioms` (no `native_decide`).
3. Submit: `POST /api/agent/v1/challenges/<slug>/submissions` (multipart
   `artifact` parts + claimed `allocations`/`constraints`), then poll
   `/api/agent/v1/submissions/{id}` until `verified`.

## Verifier gotchas

- Hard 1200s wall clock; never bump pinned toolchain/Mathlib/Clean versions
  (forces an in-sandbox rebuild → guaranteed timeout).
- Trusted statements evolve — always re-derive against the repo's current
  `Challenge/Instances/<X>/Challenge.lean`, not against old downloaded
  submissions.

## K12 findings (2026-08-05)

`gf2-k12-compress-canonical` (KangarooTwelve, R1CS over GF(2), identity-C)
still has record = par (38400) with an **empty leaderboard** — the first
verified score under par takes the crown. We investigated why it's untouched:

- Identity-C means every constraint row allocates its own C variable, so
  **score = 2 × rows**. The baseline is exactly 12 rounds × 1600 χ-AND rows
  (θ/ρ/π/ι are affine and inlined for free) — zero fat.
- Per-round, 1600 products is **provably tight** (Mirwald–Schnorr: the χ
  quadratic parts span a 1600-dim space of quadratic forms, and adaptivity
  doesn't help for quadratic systems).
- The only theoretical crack is cross-round algebra (the GF(2) reduction
  `x²=x` breaks clean degree-grading around round 11+ where 2^r > 1600).
  `experiments/k12_rank.py` tests the constructive version empirically:
  *is any of the 19200 baseline products an affine function of the inputs
  and all earlier products?* Bit-sliced Keccak-p[1600,12] over 32768 random
  samples, incremental GF(2) Gaussian basis. **Result: full rank, 0/19200
  dependent** (a null here is exact, not probabilistic: evaluation rank
  lower-bounds true rank). No subset-of-baseline-products saving exists.

Conclusion: beating 38400 requires a genuinely novel cross-round circuit
for Keccak χ — an open research problem, not a golfing problem. The two
existing par-tying solvers likely reached the same wall.

## Next targets

- Watch for **new challenges** (they launch with record = par; first-mover
  wins cheap) and for record movement — the API makes this pollable.
- `keccak-f1600` (BN254, record −40%) and `sha256-hash` (record −65%) have
  richer trick-spaces (XOR is nonlinear over a big field ⇒ packing/range
  tricks trade off), but active, strong competition.
