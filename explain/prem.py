from sage.all import gcd
from typing import Iterable
from helper import lv, lc, red, ldeg
from log import log, LogTopic

algo = 'naive'


def prem_set_algo(algorithm: str):
    global algo
    algo = algorithm


def prem(G, f, var):
    if lv(G) < var or lv(f) < var:
        log(LogTopic.WARNING, f"prem: variable missing")
    if ldeg(G, var) < ldeg(f, var):
        log(LogTopic.WARNING, f"prem: degree smaller (G: {var}^{ldeg(G, var)}, f: {var}^{ldeg(f, var)})")

    if algo == 'gcd':
        rem = prem_improved(G, f, var)
    elif algo == 'pdiv':
        rem = prem_pdiv(G, f, var)
    elif algo == 'naive':
        rem = prem_improved_naive(G, f, var)
    elif algo == 'book':
        rem = prem_book(G, f, var)
    elif algo == 'paper':
        rem = prem_paper(G, f, var)
    else:
        raise Exception("Invalid prem algo specified")
    log(LogTopic.DEBUG, f"prem of {G} divided by {f} results in {rem}")
    return rem


def pquo(G, f, var):
    if lv(G) < var or lv(f) < var:
        log(LogTopic.WARNING, f"pquo: variable missing")
    if ldeg(G, var) < ldeg(f, var):
        log(LogTopic.WARNING, f"pquo: degree smaller (G: {var}^{ldeg(G, var)}, f: {var}^{ldeg(f, var)})")

    if algo == 'gcd':
        quo = pquo_improved(G, f, var)
    elif algo == 'pdiv':
        quo = pqou_pdiv(G, f, var)
    elif algo == 'naive':
        quo = pquo_improved_naive(G, f, var)
    else:
        raise Exception("Invalid prem algo specified")
    log(LogTopic.DEBUG, f"pquo of {G} divided by {f} results in {quo}")
    return quo


def prem_iter(P: Iterable, f, var=None):
    var = var or lv(f)
    for p in P:
        yield p if lv(p) < var else prem(p, f, var)


def prem_iter_inv(G, F: Iterable, var=None):
    var = var or lv(G)
    for f in F:
        G = prem(G, f, var)
    return G


def prem_paper(Q, P, var):
    R = Q
    d = P.degree(var)
    while True:
        m = R.degree(var)
        if m < d:
            break
        I = lc(P, var)
        R = I * R - lc(R, var) * var**(m-d) * P
    return R


def prem_book(G, F, x):
    r = G.degree(x)
    h = F.degree(x)
    d = r - h + 1

    if r < h:
        return G

    L = lc(F, x)
    F = red(F, x)

    while h <= r and not G.is_zero():
        T = x ** (r - h) * F * lc(G, x)
        G = 0 if r == 0 else red(G, x)
        G = L * G - T
        r = G.degree(x)
        d -= 1
    return G * L ** d


def prem_pdiv(f, g, x):
    return pdiv(f, g, x, False)[1]


def pqou_pdiv(f, g, x):
    return pdiv(f, g, x, True)[0]


def pdiv(f, g, x, calc_quo: bool = True):
    """
    Polynomial pseudo-division (Q,R) <- (G,F,x) from densearith.py of sympy
    """
    df = f.degree(x)
    dg = g.degree(x)
    q, r, dr = 0, f, df

    if df < dg:
        return q, r

    n = df - dg + 1
    lc_g = lc(g, x)

    while True:
        lc_r = lc(r, x)
        j, n = dr - dg, n - 1

        if calc_quo:
            Q = q * lc_g
            q = Q + lc_r * (x ** j)

        R = r * lc_g
        G = g * (lc_r * (x ** j))

        r = R - G
        _dr, dr = dr, r.degree(x)

        if dr < dg:
            break
        assert dr < _dr

    c = lc_g ** n
    q = q * c
    r = r * c
    return q, r


def prem_improved_naive(G, F, var):
    Q, R = pdiv(G, F, var)
    m = F.degree(var)
    l = G.degree(var)
    I = lc(F, var) ** max(l - m + 1, 0)
    assert I * G == F * Q + R
    g = gcd([R, Q, I])
    if not g.is_constant():
        log(LogTopic.INFO, f"Removed gcd {g}")
        R //= g
        assert (I//g) * G == F * (Q//g) + R
    return R


def pquo_improved_naive(G, F, var):
    Q, R = pdiv(G, F, var)
    m = F.degree(var)
    l = G.degree(var)
    I = lc(F, var) ** max(l - m + 1, 0)
    assert I * G == F * Q + R
    g = gcd([R, Q, I])
    if not g.is_constant():
        log(LogTopic.INFO, f"Removed gcd {g}")
        Q //= g
        assert (I//g) * G == F * Q + (R//g)
    return Q


def prem_improved(uu, vv, x):
    R = x.parent()
    if (vv//x).is_constant():
        return uu.subs({x: 0})
    else:
        r, v = uu, vv
        dr, dv = ldeg(r, x), ldeg(v, x)
        if dv <= dr:
            l = v.coefficient({x: dv})  # l = lc(v, x)
            v -= l * x**dv
        else:
            return uu
        while dv <= dr and not r.is_zero():
            # _, lu, lv = xgcd(l, r.coefficient({x: dr}))
            c = r.coefficient({x: dr})
            g = gcd(l, c)
            lu, lv = l // g, c // g
            t = x**(dr-dv) * v * lv
            r = R(0) if dr == 0 else r - c * x**dr  # subs(x^dr = 0,r)
            r = lu * r - t
            dr = ldeg(r, x)
        return r


def pquo_improved(G, F, var):
    # TODO implement me
    pass
