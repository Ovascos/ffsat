from enum import Enum
from collections import deque
from typing import Callable, Optional
from .literal import toString


class TrailElementKind(Enum):
    ASSIGNMENT = 1
    FEASIBLE_UPDATE = 2
    NEW_LEVEL = 3
    NEW_STAGE = 4


class TrailElement:
    def __init__(self, kind: TrailElementKind, undo: Callable[[], None], literal: int):
        self.kind: TrailElementKind = kind
        self.literal: Optional[int] = literal
        self.undo: Callable[[], None] = undo

    def __str__(self) -> str:
        ret = f"TElem({self.kind.name}"
        if self.kind == TrailElementKind.ASSIGNMENT:
            ret += f", {toString(self.literal)}"
        return ret + ")"

    def __repr__(self) -> str:
        return self.__str__()


class Trail:
    def __init__(self):
        self.stack: deque = deque()

    def __len__(self) -> int:
        return len(self.stack)

    def __getitem__(self, item) -> TrailElement:
        return self.stack[item]

    def push(self, kind: TrailElementKind, undo: Callable[[], None], literal: Optional[int] = None):
        self.stack.append(TrailElement(kind, undo, literal))

    def pop(self) -> TrailElement:
        return self.stack.pop()

    def undo_until(self, pred: Callable[[], bool]):
        while pred() and len(self.stack) > 0:
            t: TrailElement = self.stack.pop()
            t.undo()
