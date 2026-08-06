#!/usr/bin/env python3
"""
Sampled affine-rank redundancy test over F_p, for a circuit's witness values.

Input: JSON list of samples, each {"inputs": [vals], "witnesses": [vals]} from
the WitnessDump extractor. For each witnessed cell w_k (in allocation order),
test whether its value across the samples is an AFFINE function of
{1, inputs, w_0..w_{k-1}} over F_p. If it is, w_k is redundant: the witness +
its defining constraint can be replaced by that affine expression, saving
1 alloc + (typically) 1 constraint. Each hit that repeats in a per-step gadget
multiplies by the step count.

Soundness of the *test*: an affine dependence over enough random samples holds
identically with overwhelming probability (Schwartz–Zippel: a nonzero affine
relation fails on a random point w.p. ≥ 1−1/p). Crucially a NEGATIVE (full
rank) result is EXACT — evaluation rank lower-bounds true rank — so "no
redundancy found" is a hard statement, and any positive must still be verified
symbolically before trusting the win.

This is the powerful half of the optimizer that structure-only analysis
(r1cs_analyze.py) cannot see: it finds cells that are affine combinations of
*computed* values, not just syntactic copies.
"""
import json
import sys

CIRCOM_P = 21888242871839275222246405745257275088548364400416034343698204186575808495617


def rank_redundancy(samples):
    n = len(samples)
    n_in = len(samples[0]["inputs"])
    n_wit = len(samples[0]["witnesses"])

    # column vectors (length n) over F_p
    const_col = [1] * n
    input_cols = [[samples[s]["inputs"][j] % CIRCOM_P for s in range(n)] for j in range(n_in)]
    wit_cols = [[samples[s]["witnesses"][k] % CIRCOM_P for s in range(n)] for k in range(n_wit)]

    # incremental column basis via Gaussian elimination over F_p.
    # basis: list of (pivot_row, reduced_column) with a distinct pivot row each.
    basis = []
    pivot_rows = {}

    def reduce_col(col):
        col = col[:]
        for prow, brow in basis:
            if col[prow] != 0:
                f = col[prow]
                col = [(col[i] - f * brow[i]) % CIRCOM_P for i in range(n)]
        return col

    def add_col(col):
        red = reduce_col(col)
        # find a pivot
        for i in range(n):
            if red[i] % CIRCOM_P != 0:
                inv = pow(red[i], -1, CIRCOM_P)
                norm = [(x * inv) % CIRCOM_P for x in red]
                basis.append((i, norm))
                pivot_rows[i] = True
                return True  # independent, added
        return False  # reduced to zero: dependent

    # seed the affine subspace with the constant and all input columns
    add_col(const_col)
    indep_inputs = sum(1 for c in input_cols if add_col(c))

    redundant = []
    for k, c in enumerate(wit_cols):
        if not add_col(c):
            redundant.append(k)

    return {
        "n_samples": n,
        "n_inputs": n_in,
        "n_witnesses": n_wit,
        "indep_inputs": indep_inputs,
        "redundant_witnesses": redundant,
    }


def main():
    path = sys.argv[1] if len(sys.argv) > 1 else "assertbytes_witnesses.json"
    samples = json.load(open(path))
    res = rank_redundancy(samples)
    print(f"file: {path}")
    print(f"samples {res['n_samples']}, inputs {res['n_inputs']} "
          f"({res['indep_inputs']} independent), witnesses {res['n_witnesses']}")
    if not res["redundant_witnesses"]:
        print(f"FULL RANK: all {res['n_witnesses']} witnesses affinely independent "
              f"of inputs + earlier witnesses. No affine-redundancy win exists "
              f"(exact result).")
    else:
        r = res["redundant_witnesses"]
        print(f"REDUNDANT witnesses found: {len(r)} cells {r[:40]}"
              f"{' ...' if len(r) > 40 else ''}")
        print(f"  -> each is affinely determined by earlier wires; deletable for "
              f"~2 score. VERIFY symbolically before trusting.")


if __name__ == "__main__":
    main()
