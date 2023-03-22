from collections import deque
from typing import Iterable, Deque
from itertools import combinations
from log import log, LogTopic


class FeasibleSet:
    def __init__(self, xk, all_elems: frozenset):
        self.all = all_elems
        self.xk = xk
        self.lits: Deque[int] = deque()
        self.sets: Deque[frozenset] = deque()
        # current version of the set (intersection of all previous sets)
        self.intersection: Deque[frozenset] = deque()

    def __len__(self):
        assert len(self.intersection) == len(self.sets) == len(self.lits)
        return len(self.lits)

    def push(self, literal: int, feasible: set):
        if len(self):
            new_set = feasible.intersection(self.intersection[-1])
        else:
            new_set = feasible
        self.lits.append(literal)
        self.sets.append(frozenset(feasible))
        self.intersection.append(frozenset(new_set))

    def pop(self):
        self.intersection.pop()
        self.sets.pop()
        return self.lits.pop()

    def feasible(self) -> frozenset:
        return self.intersection[-1] if self.intersection else self.all

    def feasible_element(self):
        # get random element of set
        v = None
        for v in self.feasible():
            break
        return v

    def literals(self) -> Iterable:
        return self.lits

    def literals_reduced(self) -> Iterable:
        cnt = len(self)
        log(LogTopic.TRACE, f"reducing literals from {cnt}")
        if cnt == 0:
            return []
        if cnt < 8:
            return self.literals_reduced_exact()

        target = self.feasible()
        s = [True for _ in range(cnt)]
        while True:
            improved = False
            for i in range(cnt):
                if not s[i]:
                    continue
                s[i] = False
                if self.all.intersection(*[self.sets[c] for c, v in enumerate(s) if v]) == target:
                    improved = True
                else:
                    s[i] = True
            if not improved:
                return [self.lits[i] for i in range(cnt) if s[i]]

    def literals_reduced_exact(self) -> Iterable:
        cnt = len(self)
        if cnt == 0:
            return []
        target = self.feasible()
        for n in range(cnt):
            for s in combinations(range(cnt), n+1):
                if self.all.intersection(*[self.sets[i] for i in s]) == target:
                    if len(s) < len(self):
                        log(LogTopic.TRACE, f"Improved core: {len(s)}/{len(self)}")
                    return [self.lits[i] for i in s]
        assert False
