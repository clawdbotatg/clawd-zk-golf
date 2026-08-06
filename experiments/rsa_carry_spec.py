#!/usr/bin/env python3
"""Extract the EXACT numeric soundness data of the rsa-record middle-square
grouped-carry step (GroupedEqXV.GVXHyps @ study/rsa-record/GroupedEqXV.lean:89,
instantiated as hgvxBalMiddle24 @ study/rsa-record/Params24.lean:144) into a
machine-readable JSON spec for a discrete carry-grouping optimizer.

Faithful ports of the Lean definitions (WindowCaps.lean, WindowSquare.lean,
Params24.lean). Every seed-table condition of GVXHyps is re-verified here in
exact integer arithmetic before the spec is written.

Contract being extracted (GVXHyps p L B gf posOf G V VR), with
  p  = circomPrime (BN254 scalar field)
  L  = 2*171 - 1 = 341 coefficients, base B = 24 bits
  G  = 39 groups; seed gf k = 9 (k != 37), 4 (k = 37); posOf = prefix sums
  V  = LHS side (P): caps NfP j, offsets OFFP k, widths Wf k
  VR = RHS side (N): caps NfN j, offsets OFFN k, same widths Wf k

Decidable per-boundary conditions (k < G-1), writing
  SP(k) = sum_{i<gf k} (NfP(posOf k + i) - 1) * 2^(B*i)   [and SN likewise]:
  (C1) OFFN k + OFFP k < 2^(Wf k)
  (C2P) (k=0 ? 0 : OFFP(k-1)) + 1 + SP(k) <= (OFFP k + 1) * 2^(B*gf k)
  (C2N) (k=0 ? 0 : OFFN(k-1)) + 1 + SN(k) <= (OFFN k + 1) * 2^(B*gf k)
  (C3) SP(k) + SN(k) + 2^(Wf k)*2^(B*gf k) + OFFN k * 2^(B*gf k)
        + 2^(Wf (k-1)) < p          [Lean: Wf(k-1) with Nat sub, so k=0 -> Wf 0]
Global tail conditions:
  3 <= G;  posOf(G-1) < L;  L <= posOf G
  (C4) 2^(Wf (G-3)) + sum_{t<L-posOf(G-2)} NfP(posOf(G-2)+t)*2^(B*t)
                    + sum_{t<L-posOf(G-2)} NfN(posOf(G-2)+t)*2^(B*t) < p
Cost (GroupedEqXVCost.costIs_groupedEqXV): over checked boundaries k=0..G-3,
  allocations = sum (Wf k - 1), constraints = sum (Wf k) + 1 (final assertZero).
  score = allocations + constraints.
"""
import json
import os

HERE = os.path.dirname(os.path.abspath(__file__))
OUT = os.path.join(HERE, "rsa-carry-middle-spec.json")

# ---------------------------------------------------------------- constants
# BN254 scalar field prime (circomPrime in the challenge interface)
P = 21888242871839275222246405745257275088548364400416034343698204186575808495617
B = 24
M_LIMBS = 171                     # numLimbs24
L = 2 * M_LIMBS - 1               # 341
G = 39
GW = 9                            # WindowSquare.gw (upstream window width; fixed)

# ------------------------------------------------- WindowCaps.lean ports
# rsaUniformByteShift = sum_{j<510} 2^(8j+7) + 2^4095
RSA_SHIFT = sum(1 << (8 * j + 7) for j in range(510)) + (1 << 4095)


def fixed_shift_digit(j: int) -> int:
    """fixedShiftDigit B L j (L=171): base-2^B digit j of RSA_SHIFT."""
    return (RSA_SHIFT >> (B * j)) & ((1 << B) - 1)


def fixed_bal_cap(j: int) -> int:
    """fixedBalCap 24 16 171 j."""
    d = fixed_shift_digit(j)
    top = (1 << 16) - 1 if j == M_LIMBS - 1 else (1 << B) - 1
    return max(d, top - d)


def limb_cap(tw: int, j: int) -> int:
    """limbCap B tw 171 j."""
    return (1 << tw) - 1 if j == M_LIMBS - 1 else (1 << B) - 1


def wconv(n1: int, n2: int, t, s, k: int) -> int:
    """wconv n1 n2 t s k = sum_{i<n1, i<=k, k-i<n2} t(i)*s(k-i)."""
    lo = max(0, k - n2 + 1)
    hi = min(n1 - 1, k)
    return sum(t(i) * s(k - i) for i in range(lo, hi + 1))


def window_cap(Mfun, k: int) -> int:
    """WindowSquare.windowCap 24 171 M k (gw = 9)."""
    if k % GW != 0:
        return 0
    return sum(
        wconv(M_LIMBS, M_LIMBS, Mfun, Mfun, k + e) << (B * e) for e in range(GW)
    )


# ------------------------------------------------- Params24.lean Nf tables
def nf_middle_P(j: int) -> int:
    """nfBalMiddleP24 j."""
    v = window_cap(fixed_bal_cap, j)
    if j < M_LIMBS:
        v += fixed_bal_cap(j)
    return v + 1


def nf_middle_N(j: int) -> int:
    """nfBalMiddleN24 j."""
    v = window_cap(fixed_bal_cap, j)
    v += wconv(
        M_LIMBS,
        M_LIMBS,
        lambda i: limb_cap(15, i),   # q side: 15-bit top limb
        lambda i: limb_cap(16, i),   # n side: 16-bit top limb
        j,
    )
    if j < M_LIMBS:
        v += fixed_bal_cap(j)
    return v + 1


# ------------------------------------------------- Params24.lean seed tables
def gf_seed(k: int) -> int:
    return 4 if k == 37 else 9


def pos_of_seed(k: int) -> int:
    return 9 * k if k <= 37 else 337 + 9 * (k - 38)


WTABLE = [28, 29, 30, 30, 31, 31, 31, 31, 31, 32, 32, 32, 32, 32, 32, 32, 32,
          32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 31, 31, 31, 31, 31, 30,
          30, 29, 28, 104]
OFFP_TABLE = [38045383, 76090765, 114136148, 152181531, 190226914, 228272296,
              266317679, 304363062, 342408445, 380453828, 418499210, 456544593,
              494589976, 532635359, 570680741, 608726124, 646771507, 684816890,
              714440640, 676395257, 638349874, 600304491, 562259108, 524213726,
              486168343, 448122960, 410077577, 372032195, 333986812, 295941429,
              257896046, 219850663, 181805281, 143759898, 105714515, 67669132,
              29623750, 5070757751441050188199491699395]
OFFN_TABLE = [189040317, 378080634, 567120952, 756161270, 945201588,
              1134241905, 1323282223, 1512322541, 1701362859, 1890403177,
              2079443494, 2268483812, 2457524130, 2646564448, 2835604765,
              3024645083, 3213685401, 3402725719, 3549888277, 3360847960,
              3171807642, 2982767324, 2793727006, 2604686689, 2415646371,
              2226606053, 2037565735, 1848525418, 1659485100, 1470444782,
              1281404464, 1092364146, 903323829, 714283511, 525243193,
              336202875, 147162558, 5070757751441050188199542129343]


def wf_seed(k: int) -> int:
    return WTABLE[k] if k < len(WTABLE) else 104


def offP_seed(k: int) -> int:
    return OFFP_TABLE[k] if k < len(OFFP_TABLE) else OFFP_TABLE[-1]


def offN_seed(k: int) -> int:
    return OFFN_TABLE[k] if k < len(OFFN_TABLE) else OFFN_TABLE[-1]


# ------------------------------------------------- GVXHyps verifier
def group_sum(nf, gf, pos_of, k: int) -> int:
    return sum((nf[pos_of(k) + i] - 1) << (B * i) for i in range(gf(k)))


def check_gvx(nfP, nfN, gf, pos_of, Gn, wf, offP, offN, verbose=True):
    errs = []
    # structural
    if pos_of(0) != 0:
        errs.append("posOf 0 != 0")
    for k in range(Gn + 2):
        if pos_of(k + 1) != pos_of(k) + gf(k):
            errs.append(f"posOf step broken at {k}")
        if gf(k) < 1:
            errs.append(f"gf {k} < 1")
    for k in range(Gn):
        if not (1 <= wf(k) and (1 << wf(k)) < P):
            errs.append(f"Wf bound fails at {k}")
    if not (3 <= Gn and pos_of(Gn - 1) < L and L <= pos_of(Gn)):
        errs.append("G/posOf global bounds fail")
    # per-boundary
    for k in range(Gn - 1):
        sP = group_sum(nfP, gf, pos_of, k)
        sN = group_sum(nfN, gf, pos_of, k)
        sh = B * gf(k)
        if not (offN(k) + offP(k) < (1 << wf(k))):
            errs.append(f"C1 fails at k={k}")
        prevP = 0 if k == 0 else offP(k - 1)
        prevN = 0 if k == 0 else offN(k - 1)
        if not (prevP + 1 + sP <= (offP(k) + 1) << sh):
            errs.append(f"C2P fails at k={k}")
        if not (prevN + 1 + sN <= (offN(k) + 1) << sh):
            errs.append(f"C2N fails at k={k}")
        wprev = wf(k - 1) if k > 0 else wf(0)  # Nat sub: 0-1 = 0
        if not (sP + sN + (1 << (wf(k) + sh)) + (offN(k) << sh)
                + (1 << wprev) < P):
            errs.append(f"C3 fails at k={k}")
    # tail
    base = pos_of(Gn - 2)
    tail = (1 << wf(Gn - 3)) \
        + sum(nfP[base + t] << (B * t) for t in range(L - base)) \
        + sum(nfN[base + t] << (B * t) for t in range(L - base))
    if not (tail < P):
        errs.append("C4 (tail) fails")
    if verbose:
        for e in errs:
            print("FAIL:", e)
    return errs


def cost(wf, Gn):
    alloc = sum(wf(k) - 1 for k in range(Gn - 2))
    cons = sum(wf(k) for k in range(Gn - 2)) + 1
    return alloc, cons


def main():
    nfP = [nf_middle_P(j) for j in range(L)]
    nfN = [nf_middle_N(j) for j in range(L)]

    errs = check_gvx(nfP, nfN, gf_seed, pos_of_seed, G, wf_seed,
                     offP_seed, offN_seed)
    if errs:
        raise SystemExit(f"seed verification FAILED ({len(errs)} errors)")
    alloc, cons = cost(wf_seed, G)
    print(f"seed GVXHyps verified OK: all conditions hold")
    print(f"seed cost: alloc={alloc} cons={cons} score={alloc + cons} "
          f"(carry-only score = {alloc + cons - 1})")

    spec = {
        "description": (
            "Exact numeric soundness data for the grouped-carry step of the "
            "rsa-record middle modular squaring (GroupedEqXV.GVXHyps, "
            "hgvxBalMiddle24). Nf tables are per-coefficient caps and are "
            "FIXED (grouping-independent); an optimizer may choose any "
            "(G, gf, posOf, Wf, OFFP, OFFN) satisfying the conditions."
        ),
        "source": {
            "contract": "study/rsa-record/GroupedEqXV.lean:89 (GVXHyps)",
            "instantiation": "study/rsa-record/Params24.lean:144 (hgvxBalMiddle24)",
            "cost": "study/rsa-record/GroupedEqXVCost.lean (costIs_groupedEqXV)",
        },
        "p": str(P),
        "B": B,
        "L": L,
        "m_limbs": M_LIMBS,
        "window_gw": GW,
        "NfP": [str(v) for v in nfP],
        "NfN": [str(v) for v in nfN],
        "NfP_bits": [v.bit_length() for v in nfP],
        "NfN_bits": [v.bit_length() for v in nfN],
        "constraints": {
            "vars": (
                "choose G>=3, gf:[G]->N>=1 with posOf prefix sums, posOf(G-1)<L<=posOf(G); "
                "per boundary k<G-1 choose OFFP k, OFFN k, Wf k>=1 with 2^Wf k<p"
            ),
            "SP(k)": "sum_{i<gf k} (NfP[posOf k + i]-1)*2^(B*i)  (index>=L -> Nf=1, term 0)",
            "SN(k)": "sum_{i<gf k} (NfN[posOf k + i]-1)*2^(B*i)",
            "C1": "OFFN k + OFFP k < 2^(Wf k)",
            "C2P": "(k=0?0:OFFP(k-1)) + 1 + SP(k) <= (OFFP k + 1)*2^(B*gf k)",
            "C2N": "(k=0?0:OFFN(k-1)) + 1 + SN(k) <= (OFFN k + 1)*2^(B*gf k)",
            "C3": "SP(k) + SN(k) + 2^(Wf k)*2^(B*gf k) + OFFN k*2^(B*gf k) + 2^(Wf(max(k-1,0))) < p",
            "C4": "2^(Wf(G-3)) + sum_{t<L-posOf(G-2)} (NfP+NfN)[posOf(G-2)+t]*2^(B*t) < p",
            "cost": "score = sum_{k<G-2} (2*Wf k - 1) + 1(final assertZero row)",
        },
        "seed": {
            "G": G,
            "gf": [gf_seed(k) for k in range(G)],
            "posOf": [pos_of_seed(k) for k in range(G + 1)],
            "Wf": [wf_seed(k) for k in range(G - 1)],
            "OFFP": [str(offP_seed(k)) for k in range(G - 1)],
            "OFFN": [str(offN_seed(k)) for k in range(G - 1)],
            "alloc": alloc,
            "cons": cons,
            "score": alloc + cons,
        },
    }
    with open(OUT, "w") as f:
        json.dump(spec, f, indent=1)
    print(f"wrote {OUT} ({os.path.getsize(OUT)} bytes)")

    # quick shape report for the optimizer
    print("\nNf bit-lengths at window starts (j%9==0) vs others:")
    ws = [nfP[j].bit_length() for j in range(L) if j % 9 == 0]
    os_ = [nfP[j].bit_length() for j in range(L) if j % 9 != 0]
    print(f"  NfP window-start bits: min={min(ws)} max={max(ws)}; "
          f"off-window bits: min={min(os_)} max={max(os_)}")
    wsn = [nfN[j].bit_length() for j in range(L) if j % 9 == 0]
    osn = [nfN[j].bit_length() for j in range(L) if j % 9 != 0]
    print(f"  NfN window-start bits: min={min(wsn)} max={max(wsn)}; "
          f"off-window bits: min={min(osn)} max={max(osn)}")


if __name__ == "__main__":
    main()
