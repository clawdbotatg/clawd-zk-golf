#!/usr/bin/env python3
"""
K12 (Keccak-p[1600,12]) chi-product rank experiment.

Question: in the zkGolf gf2-k12-compress-canonical baseline (19200 chi AND
rows), is ANY product row's value an affine (GF(2)) function of the 1600
circuit inputs and all EARLIER product witnesses?  Each such dependency lets
us skip allocating that row (replace the witness variable with the affine
combination), saving 1 allocation + 1 constraint = 2 score points.

Method: bit-sliced evaluation over N random input samples.  Every wire is an
N-bit integer (its value across the N samples).  We feed each chi product
vector into an incremental GF(2) Gaussian basis seeded with the constant-1
vector and the 1600 input vectors.  A product that reduces to zero against
the basis is (with overwhelming probability, and pending exact verification)
affinely dependent on {1, inputs, earlier products}.

Full rank  -> proof (exact, since eval-rank <= true rank) that no
              subset-of-baseline-products saving exists.
Deficiency -> constructive lead; verify symbolically before celebrating.
"""
import random
import sys
import time

N = 32768  # samples; must exceed 1 + 1600 + 19200 = 20801 for a meaningful test
MASK = (1 << N) - 1
random.seed(1)

# Keccak-f[1600] round constants; Keccak-p[1600,12] (K12 / KangarooTwelve)
# uses the LAST 12 (rounds 12..23).
RC = [
    0x0000000000000001, 0x0000000000008082, 0x800000000000808A,
    0x8000000080008000, 0x000000000000808B, 0x0000000080000001,
    0x8000000080008081, 0x8000000000008009, 0x000000000000008A,
    0x0000000000000088, 0x0000000080008009, 0x000000008000000A,
    0x000000008000808B, 0x800000000000008B, 0x8000000000008089,
    0x8000000000008003, 0x8000000000008002, 0x8000000000000080,
    0x000000000000800A, 0x800000008000000A, 0x8000000080008081,
    0x8000000000008080, 0x0000000080000001, 0x8000000080008008,
]

RHO = [[0, 36, 3, 41, 18],
       [1, 44, 10, 45, 2],
       [62, 6, 43, 15, 61],
       [28, 55, 25, 21, 56],
       [27, 20, 39, 8, 14]]  # RHO[x][y]


def fresh_state():
    """1600 independent random N-bit sample vectors (the free inputs)."""
    return [[[random.getrandbits(N) for _ in range(64)] for _ in range(5)]
            for _ in range(5)]  # A[x][y][z]


def theta(A):
    C = [[0] * 64 for _ in range(5)]
    for x in range(5):
        for z in range(64):
            v = 0
            for y in range(5):
                v ^= A[x][y][z]
            C[x][z] = v
    B = [[[0] * 64 for _ in range(5)] for _ in range(5)]
    for x in range(5):
        for y in range(5):
            for z in range(64):
                B[x][y][z] = A[x][y][z] ^ C[(x - 1) % 5][z] ^ C[(x + 1) % 5][(z - 1) % 64]
    return B


def rho(A):
    B = [[[0] * 64 for _ in range(5)] for _ in range(5)]
    for x in range(5):
        for y in range(5):
            r = RHO[x][y]
            for z in range(64):
                B[x][y][z] = A[x][y][(z - r) % 64]
    return B


def pi(A):
    B = [[[0] * 64 for _ in range(5)] for _ in range(5)]
    for x in range(5):
        for y in range(5):
            B[x][y] = A[(x + 3 * y) % 5][x]
    return B


def chi(A):
    """Returns (new_state, products) where products are the 1600 AND rows
    t = (1 ^ A[x+1]) & A[x+2], the baseline witness values."""
    B = [[[0] * 64 for _ in range(5)] for _ in range(5)]
    products = []
    for x in range(5):
        for y in range(5):
            for z in range(64):
                t = (A[(x + 1) % 5][y][z] ^ MASK) & A[(x + 2) % 5][y][z]
                products.append(t)
                B[x][y][z] = A[x][y][z] ^ t
    return B, products


def iota(A, rnd):
    rc = RC[rnd]
    for z in range(64):
        if (rc >> z) & 1:
            A[0][0][z] ^= MASK
    return A


class GF2Basis:
    def __init__(self):
        self.pivots = {}  # msb -> reduced row

    def add(self, v):
        """Reduce v; if nonzero, insert and return True (independent)."""
        while v:
            p = v.bit_length() - 1
            row = self.pivots.get(p)
            if row is None:
                self.pivots[p] = v
                return True
            v ^= row
        return False


def main():
    t0 = time.time()
    basis = GF2Basis()
    basis.add(MASK)  # the constant-1 function
    A = fresh_state()
    n_indep_inputs = 0
    for x in range(5):
        for y in range(5):
            for z in range(64):
                if basis.add(A[x][y][z]):
                    n_indep_inputs += 1
    print(f"inputs independent: {n_indep_inputs}/1600  ({time.time()-t0:.1f}s)", flush=True)

    total_dep = 0
    for i, rnd in enumerate(range(12, 24)):
        A = theta(A)
        A = rho(A)
        A = pi(A)
        A, products = chi(A)
        A = iota(A, rnd)
        dep = 0
        for t in products:
            if not basis.add(t):
                dep += 1
        total_dep += dep
        print(f"round {i+1:2d} (RC[{rnd}]): dependent products {dep}/1600  "
              f"(cum {total_dep}, {time.time()-t0:.1f}s)", flush=True)

    print(f"TOTAL dependent products: {total_dep}/19200")
    if total_dep == 0:
        print("FULL RANK: no subset-of-baseline-products saving exists (exact result).")
    else:
        print(f"POTENTIAL SAVING: {2*total_dep} score points below par -- verify symbolically!")


if __name__ == "__main__":
    sys.set_int_max_str_digits(100000)
    main()
