import functools
from explain import Explain
from typing import Tuple, Optional
from helper import *
from log import log, LogTopic
from .prem import prem, prem_iter


class ExplainElimFp(Explain):
    def __call__(self, P: list, Q: list, A: dict, var) -> Tuple[list, list]:
        assert len(set(vars(P)).union(vars(Q)).difference(set(A.keys()).union({var}))) == 0
        assert not any(lv(p) > var for p in P)
        assert not any(lv(q) > var for q in Q)

        # stat
        self.stat[0] += 1
        lp, lq = len(P), len(Q)
        if (lp, lq) == (0, 0): raise RuntimeError()
        elif (lp, lq) == (1, 0): self.stat[1] += 1
        elif (lp, lq) == (0, 1): self.stat[3] += 1
        elif (lp, lq) == (1, 1): self.stat[5] += 1
        elif lq == 0: self.stat[2] += 1
        elif lp == 0: self.stat[4] += 1
        else: self.stat[6] += 1

        A = {k: v for k, v in A.items() if v is not None}
        log(LogTopic.TRACE, f"explain: explaining for variable {var}\n  Assignment: {A}\n  P: {P}\n  Q: {Q}")
        FF = var.base_ring()
        M, N = triSerPR(P.copy() + [var ** len(FF) - var], Q.copy(), A, var)
        assert lv_set(M) < var
        assert lv_set(N) < var
        M = list(map(reduce_exp, M))
        N = list(map(reduce_exp, N))

        if any(m.is_constant() and not m.is_zero() for m in M) or any(n.is_zero() for n in N):
            log(LogTopic.TRACE, "explain: found infeasible input (found 0 in P or -0 in Q)")
            return [], []

        M = list(filter(lambda p: not p.is_constant(), M))
        N = list(filter(lambda p: not p.is_constant(), N))
        log(LogTopic.TRACE, f"explain: result\n  M: {M}\n  N: {N}")
        return M, N


def check(poly, var, A, neg: bool):
    assert poly.is_constant() or poly.variable() <= var
    if not poly.is_constant() and poly.variable() == var:
        return None
    R = var.parent()
    c = R(poly.subs(fixed=A))
    assert c.is_constant()
    return c.is_zero() == neg


def check_negated_poly(q, var, A: dict) -> Optional[list]:
    ret = []
    for d in range(q.degree(var)+1):
        c = q.coefficient({var: d})
        if c.is_zero():
            continue
        s = c.subs(A)
        if not s.is_zero():
            return None
        ret.append(c)
    return ret


def triSerPR(F, G, A, var):
    # avoid expending empty system
    if not F and not G:
        return [], []
    if any(f.is_constant() and not f.is_zero() for f in F) or any(g.is_constant() and g.is_zero() for g in G):
        return [], []

    assert not check_ass(F, G, A, var)

    # check if asserting poly was found
    tmp = next((f for f in F if check(f, var, A, False)), None)
    if tmp:
        return [tmp], []
    tmp = next((g for g in G if check(g, var, A, True)), None)
    if tmp:
        return [], [tmp]

    if lv_set(F) < var:
        log(LogTopic.TRACE, f"explain: Handling negated\n  G: {G}")
        # PROJ start
        tmp = next((g for g in G if lv(g) < var and g.subs(A).is_zero()), None)
        if tmp:
            return [], [tmp]
        tmp = [check_negated_poly(g, var, A) for g in G if lv(g) == var]
        tmp = list(filter(None, tmp))
        assert tmp
        return [], min(tmp, key=lambda l: len(l))
        # PROJ end
    else:
        r1, r2, r3, r4 = [], [], [], []
        # ELIM start
        F_i = [f for f in F if lv(f) == var]
        t = min(F_i, key=lambda f: f.degree(var))
        F.remove(t)
        t_ini = lc(t, var)
        # first call
        if not t_ini.is_constant():
            t_red = red(t, var)
            r1, r2 = triSerPR(F + [t_ini, t_red], G.copy(), A, var)
        # second call
        G = list(prem_iter(G, t, var))
        G.append(t_ini)
        if F_i != [t]:
            F_rem = [prem(f, t, var) if lv(f) >= var else f for f in F]
            r3, r4 = triSerPR([t] + [f for f in F_rem if f != 0], G.copy(), A, var)
        else:
            Gi = list(filter(lambda g: lv(g) == var, G))
            if Gi:
                G = list(filter(lambda g: lv(g) < var, G))
                d = ldeg(t, var)
                if d > 2:
                    log(LogTopic.WARNING, f"explain: big degree = {d}")
                G += [prem(functools.reduce(lambda a, b: a*b, [g**d for g in Gi]), t, var)]
                # G += [prem(functools.reduce(lambda a, b: a*b, [g for g in Gi]), t, var)]
            assert lv_set(F) < var
            r3, r4 = triSerPR(F.copy(), G.copy(), A, var)
        G.remove(t_ini)
        F.append(t)
        # ELIM end
        return r1 + r3, r2 + r4
