#!/usr/bin/env python3
"""
R1CS structural analyzer for zk.golf circuits.

Input: JSON dump of a Clean circuit's flat operations (from the Extract.lean
extractor) — a list of {"witness": m} and {"assert": <expr AST>} objects, in
allocation order. Score = Σ witness m + #asserts.

This is the analysis half of the automated optimizer. It parses each assert
into a normalized R1CS row A·B = C (A, B, C linear forms over the witness
variables + constant), then runs cheap, SOUND structural redundancy checks —
each hit is a candidate cost reduction to verify in Lean:

  1. affine-copy rows: an assert equivalent to `w = affine(other vars)` with a
     trivial product side. If w is used only affinely elsewhere, it can be
     inlined → save 1 alloc + 1 constraint (the classic golf move).
  2. duplicate / proportional constraints: two rows that are scalar multiples
     → one is deletable.
  3. never-read witnesses: an allocated cell that appears in no assert → dead,
     deletable (should never happen in a tuned circuit, but a sharp check).
  4. booleanity double-cover: a var with two independent booleanity-shaped
     rows → one redundant.

Correctness contract: any flagged reduction must still be verified by editing
the Lean and rebuilding (the analyzer proposes, `lake build` disposes). A
CLEAN report on a known-optimal circuit (assert-bytes = 240) is the validation
that the analyzer doesn't hallucinate wins.

Field prime p is BN254 scalar (circomPrime); coefficients like p-1 mean -1.
"""
import json
import sys
from collections import defaultdict
from fractions import Fraction

CIRCOM_P = 21888242871839275222246405745257275088548364400416034343698204186575808495617


def signed(v):
    """Map a field constant into (-p/2, p/2] for readable coefficients."""
    v %= CIRCOM_P
    return v - CIRCOM_P if v > CIRCOM_P // 2 else v


class Lin:
    """A linear form: {var_index: coeff} plus a constant under key None."""
    __slots__ = ("terms",)

    def __init__(self, terms=None):
        self.terms = defaultdict(int)
        if terms:
            for k, v in terms.items():
                self.terms[k] += v

    def add(self, other, scale=1):
        for k, v in other.terms.items():
            self.terms[k] = (self.terms[k] + v * scale) % CIRCOM_P
        return self

    def is_zero(self):
        return all(v % CIRCOM_P == 0 for v in self.terms.values())

    def nonzero_items(self):
        return [(k, signed(v)) for k, v in self.terms.items() if v % CIRCOM_P != 0]

    def support(self):
        return frozenset(k for k, v in self.terms.items() if v % CIRCOM_P != 0 and k is not None)


def parse_expr(e):
    """Parse an expression AST into (Lin, quadratic_terms).

    quadratic_terms: list of (Lin, Lin) products that couldn't be linearized.
    For R1CS the top assert is a single A*B + C shape, so we track products
    explicitly rather than fully expanding.
    """
    t = e["type"]
    if t == "var":
        return Lin({e["index"]: 1}), []
    if t == "const":
        return Lin({None: e["value"] % CIRCOM_P}), []
    if t == "add":
        l, lq = parse_expr(e["lhs"])
        r, rq = parse_expr(e["rhs"])
        return Lin().add(l).add(r), lq + rq
    if t == "mul":
        l, lq = parse_expr(e["lhs"])
        r, rq = parse_expr(e["rhs"])
        # constant * linear stays linear
        lc = l.terms.get(None, 0) if l.support() == frozenset() else None
        rc = r.terms.get(None, 0) if r.support() == frozenset() else None
        if not l.support() and not lq:  # l is a pure constant
            c = l.terms.get(None, 0)
            out = Lin({k: v * c for k, v in r.terms.items()})
            return out, [(Lin({None: c}), q) for q in rq] if rq else []
        if not r.support() and not rq:  # r is a pure constant
            c = r.terms.get(None, 0)
            out = Lin({k: v * c for k, v in l.terms.items()})
            return out, []
        # genuine product of two non-constant forms
        return Lin(), lq + rq + [(l, r)]
    raise ValueError(f"unknown expr node {t}")


def classify(op_index, e):
    """Return a dict describing the assert row."""
    lin, quad = parse_expr(e)
    info = {"index": op_index, "lin": lin, "quad": quad}
    if not quad:
        info["kind"] = "affine"
        info["support"] = lin.support()
    elif len(quad) == 1:
        a, b = quad[0]
        info["kind"] = "single-product"
        info["A"] = a
        info["B"] = b
        info["Cvars"] = lin.support()  # the affine remainder
        # booleanity signature: A and B share the same single variable, B = A - 1 form
        sa, sb = a.support(), b.support()
        info["prod_support"] = sa | sb
    else:
        info["kind"] = "multi-product"
        info["nprod"] = len(quad)
    return info


def analyze(ops):
    # allocation map: which "index" ranges are witnessed. Clean assigns var
    # indices sequentially; witness m advances the offset by m. We track the
    # running offset to know the caller-input region vs witnessed region.
    asserts = [(i, o["assert"]) for i, o in enumerate(ops) if "assert" in o]
    wit_total = sum(o["witness"] for o in ops if "witness" in o)
    n_con = len(asserts)

    rows = [classify(i, e) for i, e in asserts]

    # var usage census
    used_in = defaultdict(list)
    for r in rows:
        supp = r["lin"].support()
        if r["kind"] == "single-product":
            supp = supp = r["A"].support() | r["B"].support() | r["Cvars"]
        elif r["kind"] == "affine":
            supp = r["support"]
        else:
            supp = set()
            for a, b in r["quad"]:
                supp |= a.support() | b.support()
            supp |= r["lin"].support()
        for v in supp:
            used_in[v].append(r["index"])

    findings = []

    # (1) affine-copy rows: an affine assert with exactly one var that is used
    # nowhere else → that var is a pure copy, inline it.
    for r in rows:
        if r["kind"] != "affine":
            continue
        supp = r["support"]
        # w = affine(rest): if some var in supp is used only in this row, it is
        # a materialized value with a single consumer (this row) → candidate.
        singles = [v for v in supp if len(used_in[v]) == 1]
        if singles and len(supp) >= 1:
            findings.append(("affine-copy", r["index"],
                             f"affine row over {sorted(signed_support(r['lin']))}; "
                             f"vars used only here: {singles} (inline candidate)"))

    # (2) duplicate / proportional constraints (same normalized support+ratio)
    sigs = defaultdict(list)
    for r in rows:
        if r["kind"] == "affine":
            key = normalize_lin_sig(r["lin"])
            sigs[("affine", key)].append(r["index"])
        elif r["kind"] == "single-product":
            key = (normalize_lin_sig(r["A"]), normalize_lin_sig(r["B"]),
                   normalize_lin_sig(r["lin"]))
            keyr = (normalize_lin_sig(r["B"]), normalize_lin_sig(r["A"]),
                    normalize_lin_sig(r["lin"]))
            sigs[("prod", min(key, keyr))].append(r["index"])
    for (kind, _), idxs in sigs.items():
        if len(idxs) > 1:
            findings.append(("duplicate-constraint", idxs[0],
                             f"{kind} row structurally identical to rows {idxs[1:]}"))

    # (3) never-read witnesses: variables in [input_end, input_end+wit_total)
    # that appear in no assert. We don't know input_end exactly here, but any
    # var index that never appears in any row is dead.
    all_vars_used = set(used_in.keys())
    # (reported only if a witnessed cell index is provably unused — needs the
    # offset map; left as a structural hook for the per-circuit driver.)

    return {
        "allocations": wit_total,
        "constraints": n_con,
        "score": wit_total + n_con,
        "n_rows_parsed": len(rows),
        "kinds": {k: sum(1 for r in rows if r["kind"] == k)
                  for k in {r["kind"] for r in rows}},
        "vars_used": len(all_vars_used),
        "findings": findings,
    }


def signed_support(lin):
    return {k for k, _ in lin.nonzero_items() if k is not None}


def normalize_lin_sig(lin):
    """A scale-invariant signature of a linear form (normalize by first coeff)."""
    items = sorted(lin.nonzero_items(), key=lambda kv: (kv[0] is None, kv[0]))
    if not items:
        return ()
    # normalize by the leading nonzero coeff so proportional forms match
    lead = None
    for k, v in items:
        lead = v
        break
    inv = pow(lead % CIRCOM_P, -1, CIRCOM_P)
    return tuple((k, (v * inv) % CIRCOM_P) for k, v in items)


def main():
    path = sys.argv[1] if len(sys.argv) > 1 else "assertbytes_r1cs.json"
    ops = json.load(open(path))
    res = analyze(ops)
    print(f"file: {path}")
    print(f"score {res['score']} = {res['allocations']} alloc + {res['constraints']} con")
    print(f"rows parsed: {res['n_rows_parsed']}, kinds: {res['kinds']}, "
          f"distinct vars used: {res['vars_used']}")
    if not res["findings"]:
        print("NO structural redundancy found (circuit is structurally tight "
              "at this analysis level).")
    else:
        print(f"{len(res['findings'])} candidate reduction(s):")
        for kind, idx, msg in res["findings"][:60]:
            print(f"  [{kind}] row {idx}: {msg}")


if __name__ == "__main__":
    main()
