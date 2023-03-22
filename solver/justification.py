from typing import Set
from enum import Enum

from solver.clause import Clause


class JustificationType(Enum):
    CLAUSE = 1
    DECISION = 2
    LAZY = 3


class Justification:
    # TODO maybe solve with inheritance
    def __init__(self, type: JustificationType):
        self.type = type
        self.clause = None   # for CLAUSE only
        self.core = None     # for LAZY only

    def __str__(self) -> str:
        return f"Jst({self.type.name})"

    def __repr__(self) -> str:
        return self.__str__()


def make_justification_clause(clause: Clause) -> Justification:
    jst = Justification(JustificationType.CLAUSE)
    jst.clause = clause
    return jst


def make_justification_decision() -> Justification:
    return Justification(JustificationType.DECISION)


def make_justification_lazy(core: Set[int]) -> Justification:
    jst = Justification(JustificationType.LAZY)
    jst.core = core
    return jst
