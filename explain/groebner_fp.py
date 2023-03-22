from typing import Tuple, Optional
from sage.rings.ideal import Ideal
from sage.rings.polynomial.polynomial_ring_constructor import PolynomialRing
from explain import Explain
from log import log, LogTopic


def check_negated_poly(q, A: dict, var) -> Optional[list]:
    ret = []
    for d in range(q.degree(var) + 1):
        c = q.coefficient({var: d})
        if c.is_zero():
            continue
        s = c.subs(A)
        if not s.is_zero():
            return None
        ret.append(c)
    return ret


class ExplainGroebnerFp(Explain):
    # returns a clause falsified by A without variable var
    def __call__(self, P: list, Q: list, A: dict, var) -> Tuple[list, list]:
        log(LogTopic.TRACE, f"explain: explaining for variable {var}\n  Assignment: {A}\n  P: {P}\n  Q: {Q}")

        # Try 1: first, check the negated polynomials
        if len(Q) > 0:
            log(LogTopic.TRACE, "explain: try negative polynomials")
            for q in Q:
                r = check_negated_poly(q, A, var)
                if r is not None:
                    return [], r

        # Try 2: Eliminate x from the positive polynomials
        vs = {x for p in P for x in p.variables()}
        if len(P) > 0:
            log(LogTopic.TRACE, "explain: try positive polynomials")
            R = P[0].parent()
            assert var in vs
            assert len(vs) > 1
            RR = PolynomialRing(R.base_ring(), ",".join(str(v) for v in vs), order='lex')
            field_size = len(RR.base_ring())
            field_poly = [var ** field_size - var]
            P = [RR(p) for p in (P + field_poly)]
            # P = [RR(p) for p in P]
            I = Ideal(P)
            log(LogTopic.TRACE, f"explain: generated {I}")
            I = I.elimination_ideal(RR(var))
            log(LogTopic.TRACE, f"explain: generated elimination {I}")
            if 1 in I:
                log(LogTopic.TRACE, f"explain: found 1 in elim ideal, eliminate core")
                return [], []
            for p in I.basis:
                if p.is_constant():
                    continue
                rp = R(p)
                if not rp.subs({k: v for k, v in A.items() if v is not None}).is_zero():
                    return [rp], []

        # Try 3: Exclude the current assignment only (should not occur?)
        vs.update(x for q in Q for x in q.variables())
        vs.remove(var)
        log(LogTopic.WARNING, f"explain: WARNING: backup solution of size {len(vs)} triggered")
        assert all(val is not None for v, val in A.items() if v in vs)
        return [], [(v - val) for v, val in A.items() if v in vs]
