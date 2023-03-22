from sage.all import prod
from typing import Iterable


def vars(P: Iterable):
    return tuple(sorted(set().union(*[f.variables() for f in P]), reverse=True))


def lv(P):
    if P.is_constant():
        return None
    # TODO change with P.variable()
    l, *_ = P.variables()
    return l


def lv_set(P: Iterable):
    r = [lv(p) for p in P if lv(p) is not None]
    if len(r) == 0:
        return None
    return max(r)


def lc(P, var):
    return P.coefficient({var: P.degree(var)})


def ldeg(P, var):
    return P.degree(var)


def red(P, var):
    return P - lc(P, var) * var ** ldeg(P, var)


def reduce_exp(p):
    lb = len(p.base_ring())
    vars = p.args()
    ret = p.base_ring().zero()
    for exp, coef in p.iterator_exp_coeff():
        tmp = coef
        for v, e in zip(vars, exp):
            if e >= lb:
                e = (e % (lb-1)) or (lb-1)  # if e == 0: set e to lb-1
            tmp *= v**e
        ret += tmp
    return ret


def check_ass(F: Iterable, G: Iterable, A: dict, var) -> bool:
    FF = var.base_ring()
    return any(
        all(f.subs(A).subs({var: i}).is_zero() for f in F)
        and
        all(not g.subs(A).subs({var: i}).is_zero() for g in G)
        for i in FF
        # for i in (FF if lv_set(F) == var or lv_set(G) == var else [0])
    )


def check_ass_multi(F: Iterable, G: Iterable, A: dict, vars: list) -> bool:
    cnt = len(vars)
    if cnt == 0:
        return False
    elif cnt == 1:
        return check_ass(F, G, A, vars[0])
    else:
        var = vars[0]
        FF = var.base_ring()
        return any(check_ass_multi([f.subs({var: i}) for f in F], [g.subs({var: i}) for g in G], A, vars[1:]) for i in FF)


def reduce(p, Q):
    """
    Remove all factors of p that are in Q
    """
    R = p.parent()
    if len(Q) == 0 or p.is_constant():
        return p
    factors = {factor for (factor, power) in p.factor()}
    factors.difference_update(Q)
    return R(prod(factors))
