from test.base import TestBase
from solver.atom import Atom


class TestAtom(TestBase):
    def test_simple_1(self):
        x, y = self.genRing(13, 2)
        atom = Atom(x**4 + 3)
        assignment = {x: None, y: 3}
        ret = atom.feasible(assignment)
        self.assertEqual(len(ret), 0)
