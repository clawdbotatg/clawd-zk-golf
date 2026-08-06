#!/usr/bin/env python3
"""
Gadget synthesizer: search for single-row R1CS identities that pin a boolean
function's output bit (with booleanity implied) — the trick class behind
zk.golf's 1-row XOR3 (multiplier a+b-4c+1) and 1-row Keccak-chi
((4a+2b) - (z+3a-b-c)(4a+b+c-3) = 0).

A row is (A)·(B) = (C) with A, B, C affine in the input bits and the output z.
Two families searched:

  F1:  (z + L1(b)) · L2(b) = L3(b)
       Sound iff L2(b) != 0 for every b in the domain (then z is pinned to
       L3/L2 - L1 = f(b) pointwise, booleanity implied).
       Complete iff (f + L1)·L2 is affine as a function on the domain
       (then set L3 := that affine function).

  F2:  A(b) · B(b) = g·z + L3(b),  g != 0
       Sound always (z = (A·B - L3)/g). Complete iff A·B - g·f is affine.

Method: the completeness condition is linear in L1 once L2 is fixed (F1),
and directly checkable once A,B fixed (F2). We brute-force L2 / (A,B) over
small integer coefficient vectors and solve the residual linear system
exactly (Fractions). Known identities all have tiny coefficients, so a small
box finds them; a box sweep that comes up empty is strong (not proof-grade)
evidence of impossibility — pair with the top-monomial hand-proof method for
actual impossibility results.

Functions are given as value tables on an arbitrary product domain (default
{0,1}^n), so mixed-radix inputs (e.g. an unreduced {0,1,2} sum) work too.

Usage: python3 gadget_synth.py [--demo]
Library: search_f1(f, domains, box), search_f2(...), and pin-uniqueness
verification over Q (valid over any large-char field; coefficients are
integers so the identity transfers to F_p for p > small bound).
"""
import argparse
import itertools
import sys
from fractions import Fraction


def domain_points(domains):
    return list(itertools.product(*domains))


def affine_eval(coeffs, point):
    """coeffs = (c0, c1..cn): c0 + sum ci * b_i."""
    return coeffs[0] + sum(c * v for c, v in zip(coeffs[1:], point))


def is_affine_on(values, points, nvars):
    """Least-squares-free exact test: does an affine function interpolate
    `values` on `points`? Returns its coefficients or None.

    Solves the overdetermined system exactly with Gaussian elimination.
    """
    rows = [[Fraction(1)] + [Fraction(x) for x in pt] for pt in points]
    rhs = [Fraction(v) for v in values]
    ncols = nvars + 1
    aug = [row[:] + [r] for row, r in zip(rows, rhs)]
    pivots = []
    r = 0
    for c in range(ncols):
        piv = next((i for i in range(r, len(aug)) if aug[i][c] != 0), None)
        if piv is None:
            continue
        aug[r], aug[piv] = aug[piv], aug[r]
        pr = aug[r]
        inv = pr[c]
        aug[r] = [x / inv for x in pr]
        for i in range(len(aug)):
            if i != r and aug[i][c] != 0:
                fac = aug[i][c]
                aug[i] = [x - fac * y for x, y in zip(aug[i], aug[r])]
        pivots.append(c)
        r += 1
        if r == len(aug):
            break
    # consistency: rows with all-zero lhs must have zero rhs
    for row in aug[r:] if r < len(aug) else []:
        if all(x == 0 for x in row[:ncols]) and row[ncols] != 0:
            return None
    for i in range(len(aug)):
        if all(x == 0 for x in aug[i][:ncols]) and aug[i][ncols] != 0:
            return None
    sol = [Fraction(0)] * ncols
    for rr, c in enumerate(pivots):
        sol[c] = aug[rr][ncols]
    # verify (free columns default 0)
    for pt, v in zip(points, rhs):
        if affine_eval(sol, pt) != v:
            return None
    return sol


def search_f1(fvals, domains, box=4, l1_solver=True, progress=None):
    """Search family F1: (z + L1(b)) * L2(b) = L3(b).

    For each integer-coefficient L2 in [-box, box]^(n+1) with L2 never zero
    on the domain, solve for L1 (n+1 rational unknowns) from the linearity
    condition, then read off L3. Returns (L1, L2, L3) or None.

    Condition: (f + L1)·L2 affine  <=>  for the multilinear expansion, all
    non-affine coefficients vanish. We instead impose it directly: the values
    (f(b) + L1(b)) * L2(b) must be affine-interpolable — a linear condition
    on L1's n+1 coefficients: solve exactly.
    """
    pts = domain_points(domains)
    n = len(domains)
    f = [Fraction(v) for v in fvals]
    rng = range(-box, box + 1)
    tried = 0
    for l2 in itertools.product(rng, repeat=n + 1):
        l2v = [affine_eval(l2, pt) for pt in pts]
        if any(v == 0 for v in l2v):
            continue
        tried += 1
        if progress and tried % progress == 0:
            print(f"  ... {tried} candidate multipliers tried", file=sys.stderr)
        # unknowns: L1 coeffs u0..un.  For each point:
        #   (f + u0 + sum uj*bj) * l2v  must be affine in b -> unknowns also
        # appear in the target affine function L3 (n+1 more unknowns).
        # Set up: (f(pt)+L1(pt))*l2v(pt) - L3(pt) = 0  — linear in (L1, L3).
        ncols = 2 * (n + 1)
        aug = []
        for pt, fv, mv in zip(pts, f, l2v):
            row = [Fraction(0)] * ncols + [Fraction(-fv * mv)]
            row[0] = Fraction(mv)                       # u0 * l2v
            for j, bj in enumerate(pt):
                row[1 + j] = Fraction(mv * bj)          # uj * bj * l2v
            row[n + 1] = Fraction(-1)                   # -L3 const
            for j, bj in enumerate(pt):
                row[n + 2 + j] = Fraction(-bj)          # -L3 coeff
            aug.append(row)
        sol = solve_linear(aug, ncols)
        if sol is None:
            continue
        L1 = tuple(sol[:n + 1])
        L3 = tuple(sol[n + 1:])
        return {"family": "F1", "L1": L1, "L2": tuple(map(Fraction, l2)),
                "L3": L3, "note": f"(z + L1(b)) * L2(b) = L3(b); L2 nonzero on domain"}
    return None


def solve_linear(aug_rows, ncols):
    """Exact Gaussian elimination on augmented rows; returns any solution or
    None if inconsistent. Free variables set to 0."""
    aug = [row[:] for row in aug_rows]
    pivots = []
    r = 0
    for c in range(ncols):
        piv = next((i for i in range(r, len(aug)) if aug[i][c] != 0), None)
        if piv is None:
            continue
        aug[r], aug[piv] = aug[piv], aug[r]
        inv = aug[r][c]
        aug[r] = [x / inv for x in aug[r]]
        for i in range(len(aug)):
            if i != r and aug[i][c] != 0:
                fac = aug[i][c]
                aug[i] = [x - fac * y for x, y in zip(aug[i], aug[r])]
        pivots.append(c)
        r += 1
    for row in aug:
        if all(x == 0 for x in row[:ncols]) and row[ncols] != 0:
            return None
    sol = [Fraction(0)] * ncols
    for rr, c in enumerate(pivots):
        sol[c] = aug[rr][ncols]
    return sol


def search_f2(fvals, domains, box=4):
    """Search family F2: A(b) * B(b) = g*z + L3(b) with g != 0.

    Only reaches functions whose non-affine part is a product of two affine
    forms (degree-2-ish). Brute-force A over the box; B then solved linearly.
    """
    pts = domain_points(domains)
    n = len(domains)
    f = [Fraction(v) for v in fvals]
    rng = range(-box, box + 1)
    for a in itertools.product(rng, repeat=n + 1):
        av = [affine_eval(a, pt) for pt in pts]
        if all(v == 0 for v in av):
            continue
        # A*B - f must be affine (take g = 1; scaling is free):
        # unknowns: B (n+1), L3 (n+1):  av*B(pt) - L3(pt) = f(pt)
        ncols = 2 * (n + 1)
        aug = []
        for pt, fv, avv in zip(pts, f, av):
            row = [Fraction(0)] * ncols + [Fraction(fv)]
            row[0] = Fraction(avv)
            for j, bj in enumerate(pt):
                row[1 + j] = Fraction(avv * bj)
            row[n + 1] = Fraction(-1)
            for j, bj in enumerate(pt):
                row[n + 2 + j] = Fraction(-bj)
            aug.append(row)
        sol = solve_linear(aug, ncols)
        if sol is None:
            continue
        B = tuple(sol[:n + 1])
        L3 = tuple(sol[n + 1:])
        return {"family": "F2", "A": tuple(map(Fraction, a)), "B": B, "L3": L3,
                "note": "A(b) * B(b) = z + L3(b)"}
    return None


def verify(res, fvals, domains):
    pts = domain_points(domains)
    if res["family"] == "F1":
        for pt, fv in zip(pts, fvals):
            lhs = (Fraction(fv) + affine_eval(res["L1"], pt)) * affine_eval(res["L2"], pt)
            if lhs != affine_eval(res["L3"], pt):
                return False
            if affine_eval(res["L2"], pt) == 0:
                return False
        return True
    if res["family"] == "F2":
        for pt, fv in zip(pts, fvals):
            lhs = affine_eval(res["A"], pt) * affine_eval(res["B"], pt)
            if lhs != Fraction(fv) + affine_eval(res["L3"], pt):
                return False
        return True
    return False


def fmt(coeffs, names):
    parts = []
    if coeffs[0] != 0:
        parts.append(str(coeffs[0]))
    for c, nm in zip(coeffs[1:], names):
        if c == 0:
            continue
        parts.append(f"{'+' if c > 0 and parts else ''}{c}*{nm}")
    return " ".join(parts) if parts else "0"


def report(name, fvals, domains, box=4, skip_f2=False):
    names = [chr(ord('a') + i) for i in range(len(domains))]
    print(f"\n== {name} (domain sizes {[len(d) for d in domains]}, box ±{box})")
    if not skip_f2:
        r2 = search_f2(fvals, domains, box=min(box, 3))
        if r2 and verify(r2, fvals, domains):
            print(f"  F2 FOUND: ({fmt(r2['A'], names)}) * ({fmt(r2['B'], names)}) "
                  f"= z + ({fmt(r2['L3'], names)})")
            return r2
    r1 = search_f1(fvals, domains, box=box)
    if r1 and verify(r1, fvals, domains):
        print(f"  F1 FOUND: (z + {fmt(r1['L1'], names)}) * ({fmt(r1['L2'], names)}) "
              f"= {fmt(r1['L3'], names)}")
        return r1
    print(f"  NOT FOUND in coefficient box ±{box} (evidence of impossibility, "
          f"not proof — pair with the top-monomial argument)")
    return None


def demo():
    B2 = [(0, 1)] * 2
    B3 = [(0, 1)] * 3
    B4 = [(0, 1)] * 4
    B5 = [(0, 1)] * 5

    def tab(nbits, fn):
        return [fn(*pt) for pt in itertools.product(*([(0, 1)] * nbits))]

    # validations against known results
    report("AND (a&b)", tab(2, lambda a, b: a & b), B2)
    report("XOR2 (a^b)", tab(2, lambda a, b: a ^ b), B2)
    report("XOR3 (a^b^c) [known 1-row]", tab(3, lambda a, b, c: a ^ b ^ c), B3)
    report("chi (a ^ (~b & c)) [known 1-row]",
           tab(3, lambda a, b, c: a ^ ((1 - b) & c)), B3)
    report("parity5 [proven impossible]", tab(5, lambda *v: sum(v) % 2), B5, box=2)

    # open questions
    report("Maj3 (ab|bc|ca)", tab(3, lambda a, b, c: (a + b + c >= 2) * 1), B3)
    report("Ch (e ? f : g)", tab(3, lambda e, f, g: f if e else g), B3)
    report("XOR4", tab(4, lambda *v: sum(v) % 2), B4, box=3)
    # theta-xor with an unreduced ternary input u in {0,1,2}: z = (u + x) mod 2
    report("mod2 of u∈{0..2} plus bit x",
           [ (u + x) % 2 for u, x in itertools.product((0,1,2),(0,1)) ],
           [(0,1,2),(0,1)])
    # full ternary sum parity: z = (u+v) mod 2, u,v in {0,1,2}
    report("parity of u+v, both ∈{0..2}",
           [ (u + v) % 2 for u, v in itertools.product((0,1,2),(0,1,2)) ],
           [(0,1,2),(0,1,2)])


if __name__ == "__main__":
    ap = argparse.ArgumentParser()
    ap.add_argument("--demo", action="store_true")
    args = ap.parse_args()
    if args.demo or True:
        demo()
