from .prem import prem_pdiv
from helper import ldeg, lc


def srs(F, G, var) -> list:
    """
    Calculates a SRS H_2,...,H_r
    """
    # generate subres chain
    S = subres_chain(F, G, var)
    # remove element \mu + 1
    p1 = S.pop()
    assert p1 == F
    # remove defective
    regular = list(s for i, s in enumerate(S) if ldeg(s, var) >= i)
    assert regular
    # invert to get H_2,...,H_r
    return list(reversed(regular))


# Algorithm SubresChain from p. 13 of Wang
def subres_chain(F, G, var) -> list:
    RR = var.parent()

    # S1
    m, l = ldeg(F, var), ldeg(G, var)
    assert l <= m
    j = m - 1 if l < m else l
    S = [RR(0)] * (j+2)
    R = [RR(1)] * (j+2)
    S[j+1], S[j] = F, G
    # R[j+1] = RR(1)
    # mu = j

    while True:
        # S2
        r = -1 if S[j].is_zero() else ldeg(S[j], var)
        # loop not needed, we've initialized all S[*] with 0

        # S3
        if 0 <= r < j:
            S[r] = (lc(S[j], var)**(j-r) * S[j]) // ((R[j+1])**(j-r))
        if r <= 0:
            return S

        # S4
        I = lc(G, var) if r == m == l else RR(1)
        a = I * prem_pdiv(S[j+1], S[j], var)
        b = (-R[j+1])**(j-r+2)
        qq, rr = a.quo_rem(b)
        assert rr == 0
        S[r-1] = qq
        j = r-1
        R[j+1] = lc(S[j+1], var)
