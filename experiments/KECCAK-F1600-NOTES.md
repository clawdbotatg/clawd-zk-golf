# keccak-f1600 (BN254): why 184320 is a paradigm floor

Recon notes, 2026-08-05. Record: ordian, 184320 = 24 rounds × (3840 alloc +
3840 con). Submission `5bdce6d5-90a2-4208-bee3-0924b20ccb3b` (in `study/`).

## Ordian's per-round structure (3840 rows, 3840 allocs)

Over a big prime field XOR is nonlinear, so every fresh "bit" costs one
allocation + one R1CS row. Per round:

| stage | rows | mechanism |
|---|---|---|
| θ-C (column parities) | 320 pos × 2 | two chained single-row XOR3s |
| θ-xor (state ⊕ C₁ ⊕ rot C₂) | 1600 × 1 | single-row XOR3 |
| χ | 1600 × 1 | single-row χ identity |
| ρ, π, ι | 0 | wiring / affine |

The two magic single-row gadgets (both pin the output bit *uniquely* with
booleanity implied, because the z-multiplier never vanishes):

- **XOR3** (Verified-zkEVM/clean#395): multiplier `a + b − 4c + 1`,
  values `{±1, 2, 4, −2, ...}` — never 0.
- **χ row**: `(4a + 2b) − (z + 3a − b − c)·(4a + b + c − 3) = 0`,
  multiplier values `±1, ±2, ±3` — never 0 for `p > 3`.

## Impossibility result 1: no single-row 5-input parity

Write parity as `P = (1 − Π(1−2bᵢ))/2`. A row `(z + L₁)·L₂ = L₃` (affine L's,
`L₂ ≠ 0` on the cube) satisfied by `z = P` forces `P·L₂` to be affine
modulo `bᵢ² = bᵢ`. Expanding coefficients of the top monomial `b₁…b₅` and of
each degree-4 monomial gives `α = −Σβⱼ/2` and `βⱼ = β` const with
`16α + 32β = 0`, hence `β = 0, α = 0`, i.e. `L₂ ≡ 0`. Contradiction — in any
field of characteristic ≠ 2. So θ-C can never be 1 row per position.

## Impossibility result 2: no 2-row/1-alloc 5-input parity

Could the intermediate `t = xor3(b₁,b₂,b₃)` allocation be avoided (2 rows
pinning C directly)? No. On the valid set V = {(b, P(b))}, a row's product
side `A·B` must be affine. Reducing mod `bᵢ² = bᵢ` and `z = P`:

- the cross terms `bᵢbⱼ` (i≠j) from `l₁l₂` must vanish, and
- the degree-5 terms `Qⱼ = bⱼ·Π_{i≠j}(1−2bᵢ)` from `P·lᵢ` must cancel,

which forces every admissible row to involve **at most one input bit**
(besides z). Two such rows reference ≤ 2 of the 5 bits, so fixing those and
toggling any unreferenced bit flips the parity without changing either row —
z cannot be pinned to parity. Hence 5-parity needs ≥ 2 allocations, i.e. the
intermediate `t` is unavoidable.

## Consequence

Within the bit-materialized paradigm (state carried as boolean field
elements, θ→ρπ→χ→ι per round), the floor is exactly
`(320·2 + 1600 + 1600) = 3840` rows *and* 3840 allocations per round —
**ordian's 184320 IS the paradigm floor**. Improving the record requires
abandoning bit-materialization (packed/spread encodings all collapse back to
per-bit decompositions without lookups) or cross-round algebra — the same
class of open problem as the K12 wall (`k12_rank.py`).

## Cross-challenge intel

- The χ single-row identity and XOR3 row are directly reusable in any future
  challenge with boolean state over a big prime field.
- Interpolation rows that pin `z` uniquely via a never-vanishing affine
  multiplier are the general weapon: for an n-input boolean function, search
  for affine `L₁, L₂, L₃` with `(f + L₁)·L₂ = L₃` on the cube and `L₂ ≠ 0`.
  Existence is a small linear-algebra check (see result 1 for the
  obstruction pattern). Worth automating for any new challenge's gate set.
