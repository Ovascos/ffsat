from test.base import TestBase
from explain.prem import prem_set_algo, prem, prem_iter, pquo
from helper import *


class TestPrem(TestBase):
    def test_paper(self):
        prem_set_algo('pdiv')
        x, y, z = self.genRing(5, 3)
        g = 3*x*y**2 + y
        f = y + x
        assert x > y > z
        print(prem(g, f, x))
        print(pquo(g, f, x))
