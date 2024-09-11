#---------------------------------------------------------------------------------------------#
# Author: Robert Hines, all rights reserved
#
# Assumes m = 2**(l*lmbd) divisible by 8 and len(mu) a multiple of 8
#
# Tested for the first and third suggested parameter sets:
#   1) l=256, lmbd=256, n=1
#   2) l=1, lmbd=256, n=16 XXX
#   3) l=16, lmbd=256, n=4
#---------------------------------------------------------------------------------------------#

import os # for os.urandom()
import sys # display large integers
import time # for timing the tests

# sys.set_int_max_str_digits(2**16) # if you want "verbose" test output, not tested

#---------------------------------------#
# some algebra
#---------------------------------------#

def binary_EEA(a,b):
    """
    Binary extended Euclidean algorithm

    Return (u,v,g) with u*a+v*b = g = gcd(a,b)
    Throughout, a*si+b*ti = ri for i = 0,1.
    Assumes a, b >= 0.

    Should also work for a, b representing polynomials over GF(2)
    after replacing addition/subtraction with XOR.
    """
    k = 0
    s0 = 1
    s1 = 0
    t0 = 0
    t1 = 1

    # trivial cases
    if a == 0:
        return a
    elif b == 0:
        return a

    # pull out common power of 2
    while not ((a|b)&1):
        a >>= 1
        b >>= 1
        k += 1

    # odd starting values
    r0 = a
    r1 = b

    while r0 != r1:
        if r0&1 == 1:
            if r0 >= r1:
                r0 = r0 - r1
                s0 = s0 - s1
                t0 = t0 - t1
            else:
                r1 = r1 - r0
                s1 = s1 - s0
                t1 = t1 - t0
        else:
            r0 >>= 1
            if not ((s0|t0)&1):
                s0 >>= 1
                t0 >>= 1
            else:
                s0 = (s0+b)>>1
                t0 = (t0-a)>>1
    return (s0, t0, r0*(1<<k))

def multinv(x, m):
    """
    computes multiplicative inverse of x modulo m
    """
    X = binary_EEA(x, m)
    return X[0]

def matmult(A, B, n, m):
    """
    multiply two nxn matrices mod m
    """
    C = [[0 for i in range(n)] for j in range(n)]
    for i in range(n):
        for j in range(n):
            for k in range(n):
                C[i][j] += A[i][k] * B[k][j]
    return [[C[i][j] & (m-1) for j in range(n)] for i in range(n)]

def minor(M, i, j):
    """
    removes row i and column j from M
    """
    M = M[ : i] + M[i+1 : ]
    M = [m[ : j] + m[j+1 : ] for m in M]
    return M

def det(M, n, m):
    """
    determinant of nxn M modulo m
    recursive, expansion along first row
    """
    if n == 1:
        return M[0][0] & (m-1)
    else:
        d = 0
        for i in range(n):
            d += ((-1)**i)*M[0][i]*det(minor(M, 0, i), n-1, m) & (m-1)
        return d & (m-1)

def adjugate(M, n, m):
    """
    adjugate of nxn M modulo m
    """
    return [[((-1)**(i+j))*det(minor(M, j, i), n-1, m) & (m-1) for j in range(n)] for i in range(n)]

def inverse(M, n, m):
    """
    assumes M is invertible
    m a power of two
    """
    Mdet = det(M, n, m)
    Mdetinv = multinv(Mdet, m)
    Madj = adjugate(M, n, m)
    for i in range(n):
        for j in range(n):
            Madj[i][j] = Madj[i][j]*Mdetinv & (m-1)

    return Madj

#---------------------------------------#
# other helpers
#---------------------------------------#

def binlist2bytes(bl):
    n = len(bl)//8
    Bl = []
    for i in range(n):
        x = bl[8*i:8*(i+1)]
        y = sum([x[j]*(2**(7-j)) for j in range(8)])
        Bl.append(y)
    return bytes(Bl)

#---------------------------------------#
# key_gen, encrypt, decrypt
#---------------------------------------#

def key_gen(l, lmbd, n):

    assert l*lmbd >= 3
    m = 2**(l*lmbd)

    # random length l generators G0, G1
    L = [[1,0],[1,1]]
    R = [[1,1],[0,1]]

    g0rand = int.from_bytes(os.urandom((l+7)//8), "big")
    G0small = [[1,0],[0,1]]
    g1rand = int.from_bytes(os.urandom((l+7)//8), "big")
    G1small = [[1,0],[0,1]]

    G0bin = []
    G1bin = []

    for i in range(l):

        b0 = g0rand&1
        g0rand = g0rand>>1
        G0bin.append(b0)
        if b0 == 0:
            G0small = matmult(G0small, L, 2, m)
        else:
            G0small = matmult(G0small, R, 2, m)

        b1 = g1rand&1
        g1rand = g1rand>>1
        G1bin.append(b1)
        if b1 == 0:
            G1small = matmult(G1small, L, 2, m)
        else:
            G1small = matmult(G1small, R, 2, m)

        for i in range(2):
            for j in range(2):
                G0small[i][j] = G0small[i][j] & (m-1)
                G1small[i][j] = G1small[i][j] & (m-1)

    # print(f"G0small = {G0small}")
    # print(f"G1small = {G1small}")

    G0big = [[0 for i in range(2*n)] for j in range(2*n)]
    G1big = [[0 for i in range(2*n)] for j in range(2*n)]
    for i in range(2):
        for j in range(2):
            for k in range(n):
                G0big[n*i+k][n*j+k] = G0small[i][j]
                G1big[n*i+k][n*j+k] = G1small[i][j]

    # invertible nxn matrix S, entries modulo 2**(l*lmbd)
    invertible = False
    while not invertible:
        S = [[0 for i in range(2*n)] for j in range(2*n)]
        for i in range(2*n):
            for j in range(2*n):
                S[i][j] = int.from_bytes(os.urandom(l*lmbd//8), "big")
        Sdet = det(S, 2*n, m)
        if Sdet & 1 != 0:
            invertible = True
    Sinv = inverse(S, 2*n, m)

    # print(matmult(S, Sinv, 2*n, m))

    # S = [[1 if i==j else 0 for i in range(2*n)] for j in range(2*n)]
    # Sinv = [[1 if i==j else 0 for i in range(2*n)] for j in range(2*n)]

    # conjugate G0, G1 by S to get public key P0, P1
    # use adjugate instead to skip some computation

    P0 = matmult(matmult(Sinv, G0big , 2*n, m), S, 2*n, m)
    P1 = matmult(matmult(Sinv, G1big , 2*n, m), S, 2*n, m)

    return ((G0bin, G1bin, S, Sinv), (P0, P1))

def encrypt(mu, P0, P1, lmbd, l, n):
    """
    encrypt bytes mu of bitlength lmbd using public key P0, P1
    """

    m = 2**(l*lmbd)

    mb = int.from_bytes(mu, "big")
    C = [[1 if i == j else 0 for i in range(2*n)] for j in range(2*n)]

    for i in range(lmbd):
        b = mb&1
        mb = mb>>1
        if b == 0:
            C = matmult(P0, C, 2*n, m)
        else:
            C = matmult(P1, C, 2*n, m)

    return C

def decrypt(C, G0bin, G1bin, S, Sinv, l, lmbd, n):
    """
    decrypt C (encryption of lmbd-bit mu) using secret key G0, G1, S
    """
    m = 2**(l*lmbd)

    plain_n = matmult(matmult(S, C, 2*n, m), Sinv, 2*n, m)
    cipher00 = plain_n[0][0]
    cipher01 = plain_n[0][n]
    cipher10 = plain_n[n][0]
    cipher11 = plain_n[n][n]
    cipher = [[cipher00, cipher01], [cipher10, cipher11]]

    # start factoring...
    Linv = [[1,0],[-1,1]]
    Rinv = [[1,-1],[0,1]]
    plain_long = []

    for i in range(l*lmbd):
        # first column
        x = cipher[0][0]
        y = cipher[1][0]
        if y >= x:
            plain_long.append(0) # L
            cipher = matmult(Linv, cipher, 2, m)
        else:
            plain_long.append(1) # R
            cipher = matmult(Rinv, cipher, 2, m)

    mu = []
    # print(plain_long)
    # print(G0bin)
    # print(G1bin)
    for i in range(lmbd):
        x = plain_long[i*l : (i+1)*l]
        if x == G0bin:
            mu.append(0)
        elif x == G1bin:
            mu.append(1)
        else:
            print("decoding error ct to pt in decrypt...")

    mu_bytes = binlist2bytes(mu)
    return mu_bytes


#---------------------------------------#
# test
#---------------------------------------#

def test(l, lmbd, n, verbose = False):
    t0 = time.time()
    sk, pk = key_gen(l, lmbd, n)
    tkg = time.time()
    G0bin, G1bin, S, Sinv = sk
    P0, P1 = pk
    mu = os.urandom(lmbd//8)
    C = encrypt(mu, P0, P1, lmbd, l, n)
    tenc = time.time()
    mu_recovered = decrypt(C, G0bin, G1bin, S, Sinv, l, lmbd, n)
    t1 = time.time()
    print("\n")
    print(f"parameters: l={l}, lmbd={lmbd}, n={n}")
    print(f"elapsed time: {t1-t0} seconds")
    print(f"\tkey gen {tkg-t0}, enc {tenc-tkg}, dec {t1-tenc}")
    print("\n")
    if verbose:
        print(f"secret G0bin = {G0bin}")
        print(f"secret G1bin = {G1bin}")
        print(f"secret S = {S}")
        print(f"secret Sinv = {Sinv}")
        print("\n")
        print(f"public P0 = {P0}")
        print(f"public P1 = {P1}")
        print("\n")
        print(f"mu = 0x{mu.hex()}")
        print(f"C = {C}")
        print(f"mu_recovered = 0x{mu_recovered.hex()}")
        print("\n")
    if mu ==  mu_recovered:
        retfail = 0
        print("SUCCESS")
    else:
        retfail = 1
        print("FAILURE")
    return ((t0, tkg, tenc, t1), retfail)

# N = 100
# t = [0,0,0,0]
# failcnt = 0
# for i in range(N):
#     x, y = test(256,256,1)
#     t[0] += x[0]
#     t[1] += x[1]
#     t[2] += x[2]
#     t[3] += x[3]
#     failcnt += y
# rep1 = f"param set 1 {(t[1]-t[0])/N}, {(t[2]-t[1])/N}, {(t[3]-t[2])/N}; failures {failcnt}"
#
# t = [0,0,0,0]
# failcnt = 0
# for i in range(N):
#     x, y = test(16,256,4)
#     t[0] += x[0]
#     t[1] += x[1]
#     t[2] += x[2]
#     t[3] += x[3]
#     failcnt += y
# rep2 = f"param set 2 {(t[1]-t[0])/N}, {(t[2]-t[1])/N}, {(t[3]-t[2])/N}; failures {failcnt}"
#
# print(rep1)
# print(rep2)
