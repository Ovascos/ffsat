import functools
from typing import Tuple, List
from log import log, LogTopic
from helper import *

# variable naming convention
#  p: one polynomial =0
#  q: one polynomial !=0
#  P: set of polynomials =0
#  Q: set of polynomials !=0
#
#  A: partial assignment dict
#  var: variable to eliminate

LemmaTuple = Tuple[List, List]


def exclude_coefficient(p, var, A: dict) -> list:
    ret = list()
    for d in range(p.degree(var) + 1):
        c = p.coefficient({var: d})
        if c.is_constant():
            continue
        alpha = c.subs(A)
        ret.append(c - alpha)
    return ret


def exclude_assignment(vars: set, A: dict):
    log(LogTopic.WARNING, f"explain: backup solution of size {len(vars)} triggered")
    assert all(val is not None for v, val in A.items() if v in vars)
    return [], [(v - val) for v, val in A.items() if v in vars]


class Explain:
    def __init__(self):
        self.stat = {i: 0 for i in range(0, 7)}

    def statistics(self) -> dict:
        return self.stat.copy()

    def caseI(self, p, var, A: dict) -> LemmaTuple:
        log(LogTopic.TRACE, f"explain: I {p}")

        # todo remove me
        assert (all(not p.subs(A).subs({var: i}).is_zero() for i in var.base_ring()))

        ret = []
        for d in range(p.degree(var) + 1):
            c = p.coefficient({var: d})
            if c.is_constant():
                continue
            alpha = c.subs(A)
            ret.append(c - alpha)

        return [], ret

    # many equal
    def caseII(self, P, var, A: dict):
        log(LogTopic.DEBUG, f"explain: II {P} for {var}")
        raise NotImplementedError()

    # one negated
    def caseIII(self, q, var, A: dict) -> LemmaTuple:
        log(LogTopic.DEBUG, f"explain: III {q}")

        assert (var in q.variables())
        assert (all(q.subs(A).subs({var: i}).is_zero() for i in var.base_ring()))
        return [], exclude_coefficient(q, var, A)

    # one equal, one negated
    def caseIV(self, p, q, var, A: dict) -> LemmaTuple:
        log(LogTopic.DEBUG, f"explain: IV {p} = 0, {q} != 0")
        # ret = exclude_coefficient(p, var, A) + exclude_coefficient(q, var, A)
        ret = exclude_coefficient(p, var, A) + exclude_coefficient(q, var, A)
        return [], ret

    # many negated
    def caseV(self, Q, var, A: dict) -> LemmaTuple:
        log(LogTopic.DEBUG, f"explain: V {Q} for {var}")
        # multiply them together and reduce exponents
        q = functools.reduce(lambda a, b: a * b, Q)
        return [], exclude_coefficient(reduce_exp(q), var, A)

    # many equal, many negated
    def caseVI(self, P, Q, var, A: dict):
        log(LogTopic.DEBUG, f"explain: VI {P}, {Q} for {var}")
        raise NotImplementedError()

    def __call__(self, P: list, Q: list, A: dict, var) -> LemmaTuple:
        assert len(set(vars(P)).union(vars(Q)).difference(set(A.keys()).union({var}))) == 0
        assert not any(lv(p) > var for p in P)
        assert not any(lv(q) > var for q in Q)

        P = list(map(reduce_exp, P))
        Q = list(map(reduce_exp, Q))

        # FF = var.base_ring()
        A = {k: v for k, v in A.items() if v is not None}
        log(LogTopic.PROOF, f"explaining for variable {var}\n  Assignment = {A}\n  P({len(P)}) = {P}\n  Q({len(Q)}) = {Q}")

        # stat
        self.stat[0] += 1
        try:
            lp, lq = len(P), len(Q)
            if (lp, lq) == (0, 0):
                raise RuntimeError()
            elif (lp, lq) == (1, 0):
                self.stat[1] += 1
                M, N = self.caseI(P[0], var, A)
            elif (lp, lq) == (0, 1):
                self.stat[3] += 1
                M, N = self.caseIII(Q[0], var, A)
            elif (lp, lq) == (1, 1):
                self.stat[4] += 1
                M, N = self.caseIV(P[0], Q[0], var, A)
            elif lq == 0:
                self.stat[2] += 1
                M, N = self.caseII(P, var, A)
            elif lp == 0:
                self.stat[5] += 1
                M, N = self.caseV(Q, var, A)
            else:
                self.stat[6] += 1
                M, N = self.caseVI(P, Q, var, A)
        except RuntimeWarning:
            log(LogTopic.WARNING, f"explain: backup solution triggered")
            vs = set()
            vs.update(x for p in P for x in p.variables())
            vs.update(x for q in Q for x in q.variables())
            vs.remove(var)
            M, N = exclude_assignment(vs, A)

        # log(LogTopic.PROOF, f"generated explanation\n M = {M}\n N = {N}")

        assert lv_set(M) < var and lv_set(N) < var
        M = list(map(reduce_exp, M))
        N = list(map(reduce_exp, N))

        if any(m.is_zero() for m in M) or any(n.is_constant() and not n.is_zero() for n in N):
            log(LogTopic.WARNING, "explain: found tautology in explanation (0 in P or -0 in Q)")
            return [], []

        M = list(filter(lambda p: not p.is_constant(), M))
        N = list(filter(lambda p: not p.is_constant(), N))
        log(LogTopic.PROOF, f"explain: result\n  M({len(M)}): {M}\n  N({len(N)}): {N}")
        return M, N
