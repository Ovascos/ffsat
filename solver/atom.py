from typing import Optional, Dict, Set
from log import log, LogTopic


class Atom:
    def __init__(self, poly):
        self.p = poly

    def eval(self, assignment: Dict) -> Optional[bool]:
        p = self.p
        R = p.parent()
        # check if variable is still un-assigned
        if any(assignment.get(v, None) is None for v in p.variables()):
            return None
        result = R(p.subs(assignment))
        if result.is_constant():
            return result.is_zero()
        # unreachable
        assert False

    def top_variable(self):
        if self.p.is_constant():
            return None  # note: for all variable x: None < x
        return self.p.variable()

    def variables(self):
        return self.p.variables()

    def feasible(self, assignment: Dict) -> Set:
        # filter None from assignment (sage doesn't like that)
        log(LogTopic.TRACE, f"feasible: generate feasible for {self} with {assignment}")
        a = dict(filter(lambda kv: kv[1] is not None, assignment.items()))
        R = self.p.parent()
        FF = R.base_ring()
        p = R(self.p.subs(a))
        assert p.is_constant() or p.is_univariate()
        if p.is_constant():
            return set(self.base()) if p == 0 else set()
        p = p.univariate_polynomial()
        ret = set(-f.constant_coefficient() for f, _ in p.factor() if f.degree() == 1)
        assert all(p(f) == FF(0) for f in ret)
        return ret

    def base(self):
        return self.p.base_ring()

    def __call__(self, *args) -> Optional[bool]:
        p = self.p
        R = p.parent()
        result = R(p(*args))
        if result.is_constant():
            return result.is_zero()
        else:
            return None

    def __eq__(self, other):
        return hasattr(other, 'p') and self.p == other.p

    def __lt__(self, other):
        if not hasattr(other, 'p') or not hasattr(other, 'top_variable'):
            return False
        v1 = self.top_variable()
        v2 = other.top_variable()
        if v1 < v2:
            return True
        if v1 > v2:
            return False
        d1 = self.p.degree(v1)
        d2 = other.p.degree(v2)
        if d1 < d2:
            return True
        if d1 > d2:
            return False
        # TODO prefer positive literals here?
        return self.p < other.p

    def __hash__(self):
        return hash(self.p)

    def __str__(self) -> str:
        return f"{self.p}"

    def __repr__(self) -> str:
        return self.__str__()
