from unittest import TestCase
from typing import Optional, List
from sage.all import GF, PolynomialRing
from log import LogTopic, enable_log


class TestBase(TestCase):
    def setUp(self) -> None:
        self.FF = None
        self.R = None
        # enable_log(LogTopic.TRACE)
        # enable_log(LogTopic.DEBUG)
        enable_log(LogTopic.WARNING)
        enable_log(LogTopic.ERROR)
        enable_log(LogTopic.PROOF)
        # enable_log(LogTopic.STAT)

    def genRing(self, elem: int = 13, count: int = 4):
        self.FF = GF(elem)
        if count > 4:
            # generate x_0...x_{count-1}
            self.R = PolynomialRing(self.FF, count, 'x')
        else:
            # generate x, y, z, t
            self.R = PolynomialRing(self.FF, ['x', 'y', 'z', 't'][0:count])
        return self.R.gens()
