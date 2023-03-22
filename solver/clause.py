from typing import Iterable, Tuple


# Contains a set of boolean variables
# Using the solver instance, the boolean variables can be matched to the atoms
class Clause:
    def __init__(self, elem: Iterable[int], learned: bool = False):
        self.elem: Tuple[int] = tuple(elem)
        self.learned: bool = learned

    def top(self):
        return self.elem[-1] if self.elem else None

    def __eq__(self, other):
        return hasattr(other, 'elem') and self.elem == other.elem

    def __hash__(self):
        return hash(self.elem)

    def __str__(self) -> str:
        from .literal import toString as lstr
        return 'Clause({})'.format(', '.join(map(lstr, self.elem)))

    def __repr__(self) -> str:
        return self.__str__()

    def __iter__(self):
        return iter(self.elem)

    def __len__(self):
        return len(self.elem)
