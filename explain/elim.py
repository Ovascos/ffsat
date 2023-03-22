import functools
from typing import Tuple, Optional, Callable, Any, List, Dict
from helper import *
from log import log, LogTopic
from .explain import Explain, LemmaTuple, exclude_coefficient
from .prem import prem, pquo
from .srs import srs

SplitFunction = Callable[[List, List, Dict, Any], LemmaTuple]


class ExplainElim(Explain):
    def __init__(self, mode: str = 'reg', coefficient_exclude: bool = False):
        super().__init__()
        self.mode = mode
        self.split: SplitFunction = split_tri_ser if mode == 'tri' else split_reg_ser
        self.coefficient_exclude = coefficient_exclude

    # many equal
    def caseII(self, P, var, A: dict) -> Tuple[list, list]:
        log(LogTopic.DEBUG, f"explain: II {P} for {var}")

        assert(all(any(not p.subs(A).subs({var: i}).is_zero() for p in P) for i in var.base_ring()))

        factor = irreducible_factors(P, A)
        return self.split(P.copy(), [factor], A, var)

    # one equal, one negated
    def caseIV(self, p, q, var, A: dict) -> Tuple[list, list]:
        log(LogTopic.DEBUG, f"explain: IV {p} = 0, {q} != 0")

        # check for irreducible factors in q for x
        if self.coefficient_exclude:
            return [], exclude_coefficient(p, var, A) + exclude_coefficient(prem(q, p, var), var, A)
        else:
            factor = irreducible_factors([p], A)
            if factor != 1:
                log(LogTopic.WARNING, f"Removed irreducible factor {factor}")
            # if not p.subs(A).is_squarefree():
            #     log(LogTopic.WARNING, f"Not squarefree: {p.subs(A).factor()}")
            return self.split([p], [q, factor], A, var)

    # many equal, many negated
    def caseVI(self, P, Q, var, A: dict) -> Tuple[list, list]:
        log(LogTopic.DEBUG, f"explain: VI {P}, {Q} for {var}")
        factor = irreducible_factors(P, A)
        return self.split(P.copy(), Q + [factor], A, var)

    def caseV(self, Q, var, A: dict) -> LemmaTuple:
        if len(Q) > 10:
            raise RuntimeWarning()
        else:
            return super().caseV(Q, var, A)


def guarded_call(call: Callable[[], LemmaTuple], guard, A: dict, negated: bool) -> Optional[LemmaTuple]:
    assert guard.subs(A).is_constant()
    if guard.subs(A).is_zero() == negated:
        return None
    return call()


def split_reg_ser(F: list, G: list, A: dict, var) -> LemmaTuple:
    return split_reg_ser_impl(F, G, [], [], A, var)


# based on algorithm RegSer from Wang's book
# F list of positive polynomials
# G list of negative polynomials
# M list of positive side conditions
# N list of negative side conditions
# A current assignment
# var variable to eliminate
#
# Remark: side conditions are returned inverted to clausify implication
def split_reg_ser_impl(F: list, G: list, M: list, N: list, A: dict, var) -> LemmaTuple:
    assert F or G
    assert all(lv(m) < var for m in M) and all(lv(n) < var for n in N), "invalid side condition"
    assert not check_ass(F, G, A, var), "assignment is not excluded"
    assert check_ass(M, N, A, var), "side condition is excluded"

    # check if asserting poly was found
    if rslt := next((f for f in F if check(f, var, A, False)), None):
        return [rslt] + N, M
    if rslt := next((g for g in G if check(g, var, A, True)), None):
        return N, [rslt] + M

    # R2.2.1
    if any(f.is_constant() and not f.is_zero() for f in F) or any(g.is_constant() and g.is_zero() for g in G):
        return N, M
    F = list(f for f in F if not f.is_constant())
    G = list(g for g in G if not g.is_constant())

    p2 = None
    F_var = list(f for f in F if lv(f) == var)
    if F_var:  # |T^<k>| > 0
        # R2.2.2.1
        p2 = min(F_var, key=lambda f: f.degree(var))
        F.remove(p2)
        F_var.remove(p2)
        I = lc(p2, var)
        if not I.is_constant() and I not in N:
            if rslt := guarded_call(lambda: split_reg_ser_impl(F + [red(p2, var)], G, M + [I], N, A, var), I, A, False):
                return rslt
            G.append(I)
            N.append(I)

        # assuming that lc(p2,var) != 0 from here on
        assert ((f := lc(p2, var).subs(A)) and f.is_constant() and not f.is_zero())

        if F_var:  # |T^<k>| > 1
            # R2.2.2.2
            p1 = F_var[0]
            H = srs(p1, p2, var)
            I_h = list(lc(h, var) for h in H)

            # R2.2.2.3
            F.remove(p1)
            # F.remove(p2)  # is already removed above
            r = len(H)
            if lv(H[-1]) < var:
                assert r >= 2
                # handle H[-1] and H[-2] together
                r -= 2
                I = I_h[-2]
                if rslt := guarded_call(lambda: split_reg_ser_impl(F + [H[-1], H[-2]], G, M, N + [I], A, var), I, A, True):
                    return rslt
                M.append(I)
            for i in reversed(range(r)):
                I = I_h[i]
                if rslt := guarded_call(lambda: split_reg_ser_impl(F + [H[i]] + I_h[i + 1:], G, M, N + [I], A, var), I, A, True):
                    return rslt
                M.append(I)
            # I_1,...,I_r are zero for A
            # maybe exclude using I_r_bar here?
            assert False, "Can this happen?"

        else:  # |T^<k>| == 1
            # R2.2.3
            p1 = next((g for g in G if lv(g) == var), None)
            if p1 and lv(p2) == var:
                # R2.2.3.1
                H = srs(p1, p2, var) if ldeg(p1, var) >= ldeg(p2, var) else srs(p2, p1, var)
                I_h = list(lc(h, var) for h in H)
                r = len(H)

                # R2.2.3.2
                # F.remove(p2)  # is already removed above
                if lv(H[-1]) < var:
                    # special case remove p1
                    I = H[-1]
                    G.remove(p1)
                    if rslt := guarded_call(lambda: split_reg_ser_impl(F + [pquo(p2, I, var)], G, M, N + [I], A, var), I, A, True):
                        return rslt
                    # if rslt := guarded_call(lambda: split_reg_ser_impl(F + [p2], G, M, N + [I], A, var), I, A, True):
                    #     return rslt
                    G.append(p1)
                    M.append(I)
                    r -= 1
                for i in reversed(range(r)):
                    I = I_h[i]
                    if rslt := guarded_call(lambda: split_reg_ser_impl(F + [pquo(p2, H[i], var)] + I_h[i + 1:], G, M, N + [I], A, var), I, A, True):
                        return rslt
                    M.append(I)
    # R2.2.4
    # |T^<k>| == 0
    G_var = list(g for g in G if lv(g) == var)
    for p1 in G_var:
        I = lc(p1, var)
        G.remove(p1)
        if rslt := guarded_call(lambda: split_reg_ser_impl(F, G + [red(p1, var)], M + [I], N, A, var), I, A, False):
            return rslt
        G.append(p1)
        N.append(I)

    # coefficient elimination for p2
    return F + N, G + M + exclude_coefficient(p2, var, A) if p2 is not None else []


def split_tri_ser(F: list, G: list, A: dict, var) -> LemmaTuple:
    assert F or G
    assert not check_ass(F, G, A, var), "assignment is not excluded"

    if any(f.is_constant() and not f.is_zero() for f in F) or any(g.is_constant() and g.is_zero() for g in G):
        return [], []
    F = list(f for f in F if not f.is_constant())
    G = list(g for g in G if not g.is_constant())

    R = var.parent()
    F = list(map(R, map(reduce_exp, F)))
    G = list(map(R, map(reduce_exp, G)))

    # check if asserting poly was found
    if rslt := next((f for f in F if check(f, var, A, False)), None):
        return [rslt], []
    if rslt := next((g for g in G if check(g, var, A, True)), None):
        return [], [rslt]

    r1, r2, r3, r4 = [], [], [], []

    F_i = [f for f in F if lv(f) == var]
    # |F_i| = 0
    if not F_i:
        if rslt := next((g for g in G if lv(g) < var and g.subs(A).is_zero()), None):
            return [], [rslt]
        # multiply all poly with x together and reduce exponents
        G = list(g for g in G if lv(g) == var)
        assert G
        q = functools.reduce(lambda a, b: a * b, G)
        return [], exclude_coefficient(reduce_exp(q), var, A)

    assert any(lv(f) == var for f in F) or any(lv(g) == var for g in G)
    t = min(F_i, key=lambda f: f.degree(var))
    F.remove(t)
    F_i.remove(t)
    t_ini, t_red = lc(t, var), red(t, var)

    # first call
    if not t_ini.is_constant():
        r1, r2 = split_tri_ser(F + [t_ini, t_red], G, A, var)  # todo check G.copy() here

    # second call
    # G = list(prem_iter(G, t, var))
    # TODO find out what it means if G gets a 0 after prem
    # G = list(map(reduce_exp, prem_iter(G, t, var)))
    # if 0 in G:
    #     return r1, r2

    if F_i:
        # |F_i| > 1
        F_rem = [prem(f, t, var) if lv(f) >= var else f for f in F]
        r3, r4 = split_tri_ser([t] + [f for f in F_rem if f != 0], G + [t_ini], A, var)
    else:
        # |F_i| = 1
        # assert(not any(lv(g) in var for g in G), "Handling negated not implemented yet")
        Gi = list(filter(lambda g: lv(g) == var, G))
        if Gi:
            G = list(filter(lambda g: lv(g) < var, G))
            d = ldeg(t, var)
            if d > 1:
                log(LogTopic.WARNING, f"explain: big degree = {d}")
                # raise RuntimeWarning("infeasible")
                # G += list(prem_iter(Gi, t, var))
            G += [prem(functools.reduce(lambda a, b: a*b, [g**d for g in Gi]), t, var)]
            # G += [prem(functools.reduce(lambda a, b: a * b, [g for g in Gi]), t, var)]

        assert lv_set(F) < var

        # leaf of the recursion
        # this call should not exceed the asserting poly check, let's assert this here
        # assert(any(f for f in F if check(f, var, A, False)) or any(g for g in G if check(g, var, A, True)))
        r3, r4 = split_tri_ser(F, G + [t_ini], A, var)

    return r1 + r3, r2 + r4


def check(poly, var, A: dict, neg: bool) -> Optional[bool]:
    if not poly.is_constant() and var in poly.variables():
        return None
    R = var.parent()
    c = R(poly.subs(fixed=A))
    assert c.is_constant()
    return c.is_zero() == neg


def irreducible_factors(polys, A):
    assert len(polys) > 0
    assert all(p.subs(A).is_univariate() for p in polys)
    f = lambda p: set(a for a, _ in p.subs(A).factor())
    factors = set.intersection(*(f(p) for p in polys))
    factors = filter(lambda p: p.degree() > 1, factors)
    R = polys[0].parent()
    factor = R(1)
    for fac in factors:
        factor *= fac
    return factor
