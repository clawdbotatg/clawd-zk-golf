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

## Next target

`gf2-k12-compress` (KangarooTwelve, R1CS over GF(2), identity-C): the record
still equals par (38400) — untouched. The GF(2) SHA-256 and BLAKE3 records
both beat Flock's hand-tuned encoders, so headroom likely exists.
