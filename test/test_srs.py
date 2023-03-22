from unittest import TestCase
from sage.all import QQ, PolynomialRing, gcd

from explain import prem_set_algo
from explain.srs import subres_chain, srs
from helper import lc
from test.base import TestBase


class TestSrsBook(TestCase):
    def test_srs_1(self):
        R = PolynomialRing(QQ, "x,y,z")
        prem_set_algo('book')
        x, y, z = R.gens()
        F = -x**4 - z**3*x**2 + x**2 - z**4 + 2*z**2 - 1
        G = x**4 + z**2*x**2 - y**2*x**2 + z**4 - 2*z**2 + 1

        S = subres_chain(F, G, x)

        H = z**3 - z**2 + y**2 - 1
        self.assertEqual(F, S[-1])
        self.assertEqual(G, S[-2])
        self.assertEqual(-H * x**2, S[-3])
        self.assertEqual(H**2 * x**2, S[-4])
        self.assertEqual(H**3 * (z**4 - 2*z**2 + 1), S[-5])
        self.assertEqual(H**4 * (z**4 - 2*z**2 + 1)**2, S[-6])


class TestSrs(TestBase):
    def test_srs_paper(self):
        x, y, z = self.genRing(5, 3)
        FF = x.base_ring()
        f = x**2 + y*x + 4
        g = x*y+z
        H = srs(f, g, x)
        I = list(lc(h, x) for h in H)
        print(H)
        print(I)

        A = {y: 2, z: 2}
        self.assertNotEqual(I[0].subs(A), 0)
        self.assertNotEqual(I[1].subs(A), 0)
        ff = f.subs(A)
        gg = g.subs(A)
        sg = gcd([ff, gg])
        hh = H[1].subs(A)
        self.assertTrue(any(sg == hh*c for c in FF if c != 0))

        A = {y: 1, z: 3}
        self.assertNotEqual(I[0].subs(A), 0)
        self.assertEqual(I[1].subs(A), 0)
        ff = f.subs(A)
        gg = g.subs(A)
        sg = gcd([ff, gg])
        hh = H[0].subs(A)
        print(ff, gg, hh)
        self.assertTrue(any(sg == hh * c for c in FF if c != 0))
