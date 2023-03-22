from explain import prem_set_algo
from test.base import TestBase
from explain.elim import ExplainElim
from itertools import product


class TestElim(TestBase):
    def runit(self, A, P, Q, var):
        elim = ExplainElim()
        M, N = elim(P, Q, A, var)
        print(elim.statistics())

        self.assertTrue(all(var not in r.variables() for r in M + N))
        self.assertTrue(all(not m.subs(A).is_zero() for m in M))
        self.assertTrue(all(n.subs(A).is_zero() for n in N))
        ok = 0
        error = 0
        count = 0
        FF = var.base_ring()
        vars = [v for v in var.parent().gens() if v != var]
        print(f"Running {len(FF)**len(vars)} times")
        for V in product(FF, repeat=len(vars)):
            count += 1
            if count % len(FF)**9 == 0:
                print(f"{count}: OK: {ok}, Errors: {error}")

            A = dict(zip(vars, V))
            if all(not m.subs(A).is_zero() for m in M) and all(n.subs(A).is_zero() for n in N):
                tmpP = [p.subs(A) for p in P]
                tmpQ = [q.subs(A) for q in Q]
                if any(
                    all(p.subs({var: d}).is_zero() for p in tmpP) and all(not q.subs({var: d}).is_zero() for q in tmpQ)
                    for d in FF
                ):
                    print(f"Error: {A}")
                    error += 1
                else:
                    ok += 1
        print(f"OK: {ok}, Errors: {error} of {count}")
        self.assertEqual(0, error)

    def runall(self, P: list, Q: list, var):
        R = var.parent()
        FF = R.base_ring()
        variables = tuple(r for r in R.gens() if r < var)
        for V in product(FF, repeat=len(variables)):
            A = dict(zip(variables, V))
            if all(any(not p.subs(A).subs({var: i}).is_zero() for p in P) or any(q.subs(A).subs({var: i}).is_zero() for q in Q) for i in FF):
                self.runit(A, P, Q, var)

    def test_pos_1(self):
        x, y, z = self.genRing(13, 3)
        p = -x ** 4 - z ** 3 * x ** 2 + x ** 2 - z ** 4 + 2 * z ** 2 - 1
        q = x ** 4 + z ** 2 * x ** 2 - y ** 2 * x ** 2 + z ** 4 - 2 * z ** 2 + 1
        self.runall([p], [q], x)

    def test_pos_1a(self):
        x, y, z = self.genRing(13, 3)
        p = -x ** 4 - z ** 3 * x ** 2 + x ** 2 - z ** 4 + 2 * z ** 2 - 1
        q = x ** 4 + z ** 2 * x ** 2 - y ** 2 * x ** 2 + z ** 4 - 2 * z ** 2 + 1
        A = {y: 12, z: 1}  # -x**4 and x**4
        # A = {y: 2, z: 5}  # -x**4 + 6*x**2 - 4 and x**4 - 5*x**2 + 4
        self.runit(A, [p], [q], x)

    def test_pos_1b(self):
        x, y, z = self.genRing(13, 3)
        p = -x ** 4 - z ** 3 * x ** 2 + x ** 2 - z ** 4 + 2 * z ** 2 - 1
        q = x ** 4 + z ** 2 * x ** 2 - y ** 2 * x ** 2 + z ** 4 - 2 * z ** 2 + 1
        A = {y: 2, z: 5}  # -x**4 + 6*x**2 - 4 and x**4 - 5*x**2 + 4
        self.runit(A, [p], [q], x)

    def test_pos_1c(self):
        x, y, z = self.genRing(13, 3)
        p = -x ** 4 - z ** 3 * x ** 2 + x ** 2 - z ** 4 + 2 * z ** 2 - 1
        q = x ** 4 + z ** 2 * x ** 2 - y ** 2 * x ** 2 + z ** 4 - 2 * z ** 2 + 1
        A = {y: 0, z: 12}
        self.runit(A, [p], [q], x)

    def test_pos_1d(self):
        x, y, z = self.genRing(13, 3)
        p = -x ** 4 - z ** 3 * x ** 2 + x ** 2 - z ** 4 + 2 * z ** 2 - 1
        q = x ** 4 + z ** 2 * x ** 2 - y ** 2 * x ** 2 + z ** 4 - 2 * z ** 2 + 1
        A = {y: 1, z: 0}
        self.runit(A, [p], [q], x)

    def test_pos_2(self):
        x,y,z = self.genRing(13, 3)
        p = [-3*x*y**3*z + 3*x*y**2 + x**2, -6*y**2*z**3 + 2*x**3*z + 5*x*y**2*z - 5*x**2*z + 4*x*y]
        q = []
        A = {y: 4, z: 3}
        self.runit(A, p, q, x)

    def test_neq_1(self):
        x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10 = self.genRing(3, 11)
        A = {x1: 1, x2: 1, x3: 1, x4: 1, x5: 1, x6: 1, x7: 1, x8: 1, x9: 1, x10: 1}
        Q = [
            x0**2 * x1**2 * x2**2 * x3**2 * x4**2 * x6 * x8**2 * x9**2 * x10**2 - x1**2 * x2**2 * x5**2 * x6 * x7**2 * x8**2 * x9**2 * x10**2,
            x0
        ]
        self.runit(A, [], Q, x0)

    def test_neq_2(self):
        # Test with wrap around:
        # when both polynomials multiplied have x0**1 and x0**3 which coefficient's cancel out but are both not zero
        x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10 = self.genRing(3, 11)
        A = {}
        Q = [

        ]
        self.runit(A, [], Q, x0)

    def test_neq_3(self):
        # Test with wrap around
        x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10 = self.genRing(3, 11)
        A = {}
        Q = [

        ]
        self.runit(A, [], Q, x0)

    def test_neq_4(self):
        # Test without wrap around
        x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10 = self.genRing(3, 11)
        A = {}
        Q = [

        ]
        self.runit(A, [], Q, x0)

    def test_neq_5(self):
        # Test with some positive without x0
        x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10 = self.genRing(3, 11)
        A = {}
        P = [

        ]
        Q = [

        ]
        self.runit(A, P, Q, x0)

    def test_neq_full_1(self):
        x4, x5 = self.genRing(211, 2)
        A = {x5: 0}
        P = []
        Q = [
             43*x4**2 + 102*x5 - 5, 72*x4 + 98, 9*x4**2 - 23*x4 + 35*x5 + 23, 72*x4 - 18, 38*x4 - 49, 38*x4 + 58,
             72*x4 + 49, -11*x4, 72*x4 - 76, 72*x4 - 23, 9*x4**2 - 23*x4 + 35*x5 + 62, 72*x4 - 72, 38*x4 - 56,
             9*x4**2 - 23*x4 + 35*x5 + 39, 43*x4**2 + 102*x5 + 39, 9*x4**2 - 23*x4 + 35*x5 + 10,
             9*x4**2 - 23*x4 + 35*x5 - 2, 9*x4**2 - 23*x4 + 35*x5 - 35, 9*x4**2 - 23*x4 + 35*x5 + 73,
             72*x4 - 28, 9*x4**2 - 23*x4 + 35*x5 - 22, 72*x4 - 100, 38*x4 + 31, 43*x4**2 + 102*x5 + 89,
             38*x4 + 97, 72*x4 + 39, 43*x4**2 + 102*x5 - 79, 72*x4 - 101, 43*x4**2 + 102*x5 - 55, 38*x4 - 73,
             43*x4**2 + 102*x5 + 57, 72*x4 - 39, 43*x4**2 + 102*x5 - 4, 38*x4 + 21, 43*x4**2 + 102*x5 - 71,
             72*x4 + 101, 38*x4 - 41, 9*x4**2 - 23*x4 + 35*x5 + 25, 43*x4**2 + 102*x5 + 38, 43*x4**2 + 102*x5 - 70,
             38*x4 + 18, 72*x4 - 49, 72*x4 + 57, 43*x4**2 + 102*x5 + 104, 72*x4 - 87, 38*x4 + 45, 38*x4 - 58,
             43*x4**2 + 102*x5 - 96, 43*x4**2 + 102*x5 + 72, 72*x4 + 18, 9*x4**2 - 23*x4 + 35*x5 - 73, 72*x4 - 20,
             43*x4**2 + 102*x5 - 93, 43*x4**2 + 102*x5 - 11, 43*x4**2 + 102*x5 + 12, 9*x4**2 - 23*x4 + 35*x5 + 104,
             43*x4**2 + 102*x5 - 13, 72*x4 + 86, 38*x4 - 37, 38*x4 + 63, 38*x4 + 60, 43*x4**2 + 102*x5 - 36,
             9*x4**2 - 23*x4 + 35*x5 - 18, 72*x4 + 75, 43*x4**2 + 102*x5 - 59, 9*x4**2 - 23*x4 + 35*x5 - 100,
             9*x4**2 - 23*x4 + 35*x5 + 94, 72*x4 - 30, 72*x4 + 81, 72*x4 + 70, 43*x4**2 + 102*x5 + 90,
             9*x4**2 - 23*x4 + 35*x5 - 27, 9*x4**2 - 23*x4 + 35*x5 - 69, 43*x4**2 + 102*x5 - 24, 43*x4**2 + 102*x5 + 27,
             38*x4 - 48, 38*x4 + 26, 72*x4 - 63, 72*x4 + 55, 72*x4 + 76, 9*x4**2 - 23*x4 + 35*x5 - 99, 38*x4 - 30,
             72*x4 + 4, 72*x4 + 30, 72*x4 + 99, 9*x4**2 - 23*x4 + 35*x5 - 49, 43*x4**2 + 102*x5 + 50,
             43*x4**2 + 102*x5 + 92, 9*x4**2 - 23*x4 + 35*x5 + 43, 43*x4**2 + 102*x5 + 48, 43*x4**2 + 102*x5 + 10,
             9*x4**2 - 23*x4 + 35*x5 + 40, 38*x4 + 34, 9*x4**2 - 23*x4 + 35*x5 + 19, 9*x4**2 - 23*x4 + 35*x5 - 75,
             72*x4 + 82, 72*x4 - 73, 38*x4 - 21, 38*x4 + 88, 9*x4**2 - 23*x4 + 35*x5 + 61, 72*x4 + 72, 72*x4 + 17,
             9*x4**2 - 23*x4 + 35*x5 - 93, 9*x4**2 - 23*x4 + 35*x5 + 59, 72*x4 + 78, 9*x4**2 - 23*x4 + 35*x5 + 20,
             38*x4 + 12, 9*x4**2 - 23*x4 + 35*x5 - 34, 9*x4**2 - 23*x4 + 35*x5 + 84, 38*x4 - 84, 43*x4**2 + 102*x5 + 75,
             38*x4 - 44, 72*x4 - 46, 43*x4**2 + 102*x5 + 85, 43*x4**2 + 102*x5 + 2, 43*x4**2 + 102*x5 + 23, 72*x4 - 51,
             43*x4**2 + 102*x5 - 58, 72*x4 + 56, 43*x4**2 + 102*x5 + 63, 9*x4**2 - 23*x4 + 35*x5 + 79, 72*x4 - 89,
             43*x4**2 + 102*x5 - 14, 9*x4**2 - 23*x4 + 35*x5 + 85, 9*x4**2 - 23*x4 + 35*x5 - 65, 43*x4**2 + 102*x5 + 77,
             72*x4 + 51, 43*x4**2 + 102*x5 - 87, 72*x4 - 70, 9*x4**2 - 23*x4 + 35*x5 + 51, 72*x4 - 56,
             43*x4**2 + 102*x5 - 45, 72*x4 - 22, 9*x4**2 - 23*x4 + 35*x5 - 38, 43*x4**2 + 102*x5 + 97,
             9*x4**2 - 23*x4 + 35*x5 - 81, 38*x4 + 36, 9*x4**2 - 23*x4 + 35*x5 + 76, 38*x4 + 68, 38*x4 - 60,
             43*x4**2 + 102*x5 - 105, 9*x4**2 - 23*x4 + 35*x5 - 21, 43*x4**2 + 102*x5 + 98, 38*x4 + 103,
             9*x4**2 - 23*x4 + 35*x5 - 15, 72*x4 - 13, 43*x4**2 + 102*x5 - 44
        ]
        self.runit(A, P, Q, x4)

    def test_mixed_0(self):
        x3, x4, x5 = self.genRing(211, 3)
        A = {x4: 165, x5: 0}
        P = [-4*x3 - 37*x4]
        Q = [78*x3**2 - 90*x3*x4 - 20*x5 + 63]
        self.runit(A, P, Q, x3)

    def test_mixed_1(self):
        x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13 = self.genRing(3, 14)
        A = {x1: 1, x2: 1, x3: 1, x4: 1, x5: 1, x6: 1, x7: 1, x8: 1, x9: 1, x10: 1, x11: 1, x12: 1, x13: 1}
        # A = {x1: 1, x2: 1, x3: 1, x4: 0, x5: 0, x6: 0, x7: 1, x8: 2, x9: 1, x10: 1, x11: 1, x12: 1, x13: 2}
        # A = {x1: 1, x2: 1, x3: 1, x4: 0, x5: 0, x6: 0, x7: 1, x8: 1, x9: 1, x10: 1, x11: 1, x12: 1, x13: 1}

        P = [x1**2*x2**2*x3*x5**2*x6**2*x11**2*x12*x13**2 - x0*x1**2*x2*x3*x4*x5*x6*x8*x11*x12**2*x13 - x1**2*x2*x3*x4*x5**2*x6*x11*x12**2*x13 + x0*x1*x2*x3*x5*x6**2*x8*x11*x12**2*x13 - x0*x1*x2*x3*x5*x6*x8*x10*x11*x12**2*x13 - x2**2*x3*x7**2*x9**2*x11**2*x12*x13**2 + x1*x2*x3*x5**2*x6**2*x11*x12**2*x13 - x1*x2*x3*x5**2*x6*x10*x11*x12**2*x13 + x0**2*x1**2*x3*x4**2*x8**2*x12 + x0**2*x1**2*x3*x6**2*x8**2*x12 + x0**2*x1**2*x3*x6*x8**2*x10*x12 - x0*x1**2*x3*x4**2*x5*x8*x12 - x0*x1**2*x3*x5*x6**2*x8*x12 + x0**2*x1*x3*x4*x6*x8**2*x12 - x0*x1**2*x3*x5*x6*x8*x10*x12 - x0**2*x1*x3*x4*x8**2*x10*x12 + x1**2*x3*x4**2*x5**2*x12 + x1**2*x3*x5**2*x6**2*x12 - x0*x1*x3*x4*x5*x6*x8*x12 + x1**2*x3*x5**2*x6*x10*x12 + x0*x1*x3*x4*x5*x8*x10*x12 + x0**2*x3*x8**2*x10**2*x12 + x1*x3*x4*x5**2*x6*x12 - x1*x3*x4*x5**2*x10*x12 - x0*x3*x5*x8*x10**2*x12 + x3*x5**2*x10**2*x12]
        Q = [x0, -x0**2*x1**2*x3**2*x8**2 + x0*x1**2*x3**2*x5*x8 - x1**2*x3**2*x5**2]

        self.runit(A, P, Q, x0)

    def test_mixed_2(self):
        # Test with negative wrap around and positive elim (both have x0)
        x0, x1, x2 = self.genRing(3, 3)
        A = {x1: 1, x2: 1}
        P = [x0*x1*x2]
        Q = [-x0-1, x0]
        self.runit(A, P, Q, x0)

    def test_mixed_3(self):
        # no solution
        x3, x4 = self.genRing(3, 2)
        A = {x4: 2}
        P = [-x3 ** 2 + x3 * x4 - x4 ** 2]
        Q = [-x3, -x3 * x4 ** 2 - x4]
        self.runit(A, P, Q, x3)

    def test_mixed_4(self):
        x6, x7, x8, x9 = self.genRing(3, 4)
        A = {x7: 0, x8: 1, x9: 1}
        P = [2*x6**3 + 2*x6**2*x9, -x6**4*x9**2 + x6**3*x9**3 - 2*x6**2*x7*x9**3 + 2*x6*x7*x9**4]
        Q = [x6]
        self.runit(A, P, Q, x6)

    def test_mixed_5(self):
        x, y, z = self.genRing(13, 3)
        P = [-x ** 4 * z ** 2 - 2 * y ** 5 + 4 * x ** 3 + 2 * x ** 2 + 5 * z ** 2]
        Q = [-4 * x ** 3 * y * z ** 2 + 4 * y ** 4 * z + 4 * x * z ** 3 + 4 * x ** 2 * y,
             4 * x ** 4 * y ** 2 - 5 * x * y ** 4 * z + 2 * x ** 4 * z ** 2 - 5 * x ** 2 * z ** 4 - 4 * z,
             -6 * z ** 6 + 3 * x ** 2 * y ** 2 - y ** 2 * z + 4 * y ** 2]
        A = {y: 5, z: 5}
        self.runit(A, P, Q, x)

    def test_mixed_6(self):
        x, y, z = self.genRing(13, 3)
        P = [5 * x ** 3 * z ** 2 - 2 * y ** 3 * z ** 2 + 5 * y ** 2 * z ** 2 + x * y * z + x * z]
        Q = [5 * y ** 3 * z ** 2 + 3 * x ** 3 + 2 * x * y ** 2 - z ** 3 - 6 * x * y,
             6 * y ** 4 * z ** 2 - 4 * y ** 2 * z ** 4 + 4 * x * z ** 2 + 2 * z ** 3]
        A = {y: 3, z: 4}
        self.runit(A, P, Q, x)

    def test_mixed_7(self):
        # fails without q**d
        x, y, z = self.genRing(13, 3)
        P = [2 * x ** 2 * y ** 3 - 6 * x * z ** 3 - 2 * y * z ** 2 + z ** 3 + 4 * x * z]
        Q = [x ** 4 * z ** 2 - 4 * x ** 3 * y - 6 * x ** 2 * y ** 2 - 4 * y ** 4 - 2 * y ** 2 * z,
             2 * x ** 4 * z ** 2 - 4 * x * y ** 2 * z ** 3 - 6 * y * z ** 3 + x * y ** 2 + 5 * z]
        A = {y: 11, z: 0}
        self.runit(A, P, Q, x)

    def test_mixed_8(self):
        # the first two polynomials of Q are not necessary
        x, y, z = self.genRing(13, 3)
        P = [2 * y ** 5 * z + 2 * x ** 3 * z ** 3 + 2 * x * y ** 2 * z ** 2 - 3 * x ** 2 * y * z - x ** 2 * z ** 2]
        Q = [
             # -5 * x ** 5 * y + x ** 3 * y * z ** 2 + y ** 4 * z ** 2 - 2 * y ** 3 * z + 3 * y ** 2 * z ** 2,
             # 5 * x ** 4 - 3 * x ** 2 * y ** 2 - x ** 2 * y * z - 2 * x * y ** 2,
             -x ** 2 * z ** 3 + 5 * x * y ** 2 * z + 5 * x * y * z ** 2 + 6 * z ** 3
             ]
        A = {y: 2, z: 5}
        self.runit(A, P, Q, x)

    def test_mixed_8_not_redundant(self):
        # test_mixed_8 without the redundant polynomials
        x, y, z = self.genRing(13, 3)
        P = [2 * y ** 5 * z + 2 * x ** 3 * z ** 3 + 2 * x * y ** 2 * z ** 2 - 3 * x ** 2 * y * z - x ** 2 * z ** 2]
        Q = [-x ** 2 * z ** 3 + 5 * x * y ** 2 * z + 5 * x * y * z ** 2 + 6 * z ** 3]
        A = {y: 2, z: 5}
        self.runit(A, P, Q, x)

    def test_mixed_9(self):
        x, y, z = self.genRing(13, 3)
        P = [4 * x ** 2 * y - 5 * x * z ** 2 + 6]
        Q = [
            (y ** 5 * z + x ** 3 * y ** 2 + 3 * y ** 4 + 3 * x ** 3 * z - 2 * x * y),
            (3 * x ** 2 * y ** 4 - 3 * x ** 3 * y * z ** 2 - 5 * y ** 3 * z ** 3 - 4 * x * y * z ** 4 - 4 * x * y ** 4),
            (-4 * x ** 5 - 3 * x ** 4 + 2 * x ** 2 * y ** 2 + 2 * x * y ** 3 - 6 * x * y * z ** 2)
        ]
        A = {y: 5, z: 8}
        self.runit(A, P, Q, x)

    def test_mixed_9_not_redundant(self):
        x, y, z = self.genRing(13, 3)
        P = [4 * x ** 2 * y - 5 * x * z ** 2 + 6]
        Q = [y ** 5 * z + x ** 3 * y ** 2 + 3 * y ** 4 + 3 * x ** 3 * z - 2 * x * y]
        A = {y: 5, z: 8}
        self.runit(A, P, Q, x)

    def test_mixed(self):
        # TODO build test with two P and one Q and x0 != 0
        pass

    def test_mixed_10(self):
        x4, x5 = self.genRing(211, 2)
        A = {x5: 36}
        P = [76*x4**10 + 96*x4**9 + 42*x4**8*x5 - 33*x4**8 + 71*x4**7*x5 - 3*x4**6*x5**2 + x4**7 - 73*x4**6*x5 + 81*x4**5*x5**2 - 2*x4**4*x5**3 - 77*x4**6 + 43*x4**5*x5 - 71*x4**4*x5**2 + 43*x4**3*x5**3 + 34*x4**2*x5**4 - 31*x4**5 - 34*x4**4*x5 + 19*x4**3*x5**2 - 31*x4**2*x5**3 + 103*x4*x5**4 + 4*x5**5 + 59*x4**4 - 22*x4**3*x5 + 55*x4**2*x5**2 - 81*x4*x5**3 - 21*x5**4 + 48*x4**3 + 60*x4**2*x5 - 2*x4*x5**2 - 42*x5**3 - 57*x4**2 - 82*x4*x5 + 23*x5**2 - 32*x4 + 18*x5 + 100]
        Q = [
            43 * x4**2 + 102 * x5 - 13,
            -102 * x4**6 + 91 * x4**5 + 81 * x4**4 * x5 - 10 * x4**4 + 35 * x4**3 * x5 + 95 * x4**2 * x5**2 + 32 * x4**3 + 102 * x4**2 * x5 - 21 * x4 * x5**2 + 40 * x5**3 + 64 * x4**2 + 66 * x4 * x5 + 18 * x5**2 - 20 * x4 + 66 * x5 - 93
        ]
        self.runit(A, P, Q, x4)

    def test_paper(self):
        x, y, z = self.genRing(5, 3)
        p = x**2+x*y+4
        q = x*y+z
        A = {y: 1, z: 3}
        print(p.subs(A))
        print(q.subs(A))
        for i in range(0, 5):
            print(p.subs(A).subs({x: i}), q.subs(A).subs({x: i}))
        self.runit(A, [p], [q], x)

    # def test_mixed_3(self):
    #     # test case incorrect (1,1,-1) is a valid zero
    #     x0, x1, x2 = self.genRing(3, 3)
    #     A = {x1: 1, x2: 1}
    #     p = 2 * x0 ** 3 + 2 * x0 ** 2 * x2
    #     Q = [2 * x0 ** 2 * x1 ** 3 - 2 * x0 ** 3 * x2 ** 2 + 1, x0]
    #     q = Q[0] * Q[1]
    #     assert all(not p.subs(A).subs({x0: i}).is_zero() and q.subs(A).subs({x0: i}).is_zero() for i in [0,1,2])
    #     self.runit(A, [p], [q], x0)

    # def test_complicated_3(self):
    #     x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15 = self.genRing(3, 16)
    #     A = {x1: 1, x2: 2, x3: 2, x4: 1, x5: 1, x6: 1, x7: 1, x8: 1, x9: 1, x10: 1, x11: 1, x12: 1, x13: 1, x14: 1, x15: 1}
    #     P = [-x0 * x2 * x3 * x4 * x6 * x8 * x13 * x14**2 * x15 + x0**2 * x3 * x4 * x9 * x11 * x13 * x14**2 * x15 + x0 * x1 * x2**2 * x4 * x8 * x10 * x14 + x0 * x2**2 * x4 * x6 * x8 * x14 - x0 * x1 * x2 * x4 * x5 * x10 * x14 - x0 * x2 * x4 * x5 * x6 * x14 - x0 * x1 * x4 * x10 * x12 * x14 - x0 * x4 * x6 * x12 * x14]
    #     Q = [
    #         x0,
    #         -x0**2 * x1 * x3**2 * x4 * x6**2 * x8**2 * x9**2 * x10 * x11**2 * x14**2 - x0**2 * x1 * x2 * x3**2 * x4 * x6**2 * x8**2 * x9 * x10 * x11 * x13 * x14**2 + x0 * x1 * x3**2 * x4 * x6**2 * x8**2 * x9**2 * x10 * x11**2 * x14**2 * x15 - x0**2 * x1**2 * x3**2 * x4 * x6**2 * x8**2 * x9 * x10**2 * x11 * x13 + x0**2 * x1**2 * x2 * x3**2 * x4 * x6**2 * x8**2 * x10**2 * x13**2 + x0 * x1**2 * x3**2 * x4 * x6**2 * x8**2 * x9 * x10**2 * x11 * x13 * x15 + x0**2 * x1**2 * x2 * x3**2 * x4 * x6**2 * x8**2 * x10**2 * x15**2 + x0**2 * x1 * x2**2 * x3**2 * x4 * x6**2 * x8**2 * x10 * x14**2 - x0 * x1 * x3**2 * x4 * x6 * x8 * x9**2 * x10 * x11**2 * x13 * x14**2 - x0 * x1 * x2**2 * x3**2 * x4 * x6**2 * x8**2 * x10 * x14**2 * x15 - x0**2 * x1 * x2 * x3**2 * x4 * x6 * x8 * x9 * x10 * x11 * x14**2 * x15 + x0 * x1 * x3**2 * x4 * x6**2 * x9**2 * x10 * x11**2 * x14**2 * x15 + x0**2 * x1**2 * x2 * x3**2 * x4 * x6**2 * x8**2 * x10**2 - x0 * x1**2 * x3**2 * x4 * x6 * x8 * x9 * x10**2 * x11 * x13**2 - x0**2 * x3**2 * x4 * x6 * x8**2 * x9**2 * x11**2 * x14**2 - x0**2 * x2 * x3**2 * x4 * x6 * x8**2 * x9 * x11 * x13 * x14**2 - x0 * x3**2 * x4 * x6**2 * x8 * x9**2 * x11**2 * x13 * x14**2 + x0 * x1**2 * x2 * x3**2 * x4 * x6**2 * x8**2 * x10**2 * x15 - x0**2 * x1**2 * x3**2 * x4 * x6 * x8 * x9 * x10**2 * x11 * x15 - x0**2 * x1**2 * x2 * x3**2 * x4 * x6 * x8 * x10**2 * x13 * x15 - x0**2 * x2 * x3**2 * x4 * x6**2 * x8 * x9 * x11 * x14**2 * x15 + x0 * x3**2 * x4 * x6 * x8**2 * x9**2 * x11**2 * x14**2 * x15 - x0 * x1**2 * x3**2 * x4 * x6 * x8 * x9 * x10**2 * x11 * x15**2 + x0**2 * x1 * x3**2 * x4 * x6 * x8**2 * x9 * x10 * x11 * x13 - x0**2 * x1 * x2 * x3**2 * x4 * x6 * x8**2 * x10 * x13**2 + x0 * x1 * x3**2 * x4 * x6**2 * x8 * x9 * x10 * x11 * x13**2 + x0 * x1 * x2 * x3**2 * x4 * x6 * x8 * x9 * x10 * x11 * x14**2 - x0**2 * x1 * x3**2 * x4 * x9**2 * x10 * x11**2 * x14**2 - x0 * x1 * x2**2 * x3**2 * x4 * x6 * x8 * x10 * x13 * x14**2 + x0**2 * x1 * x3**2 * x4 * x6**2 * x8 * x9 * x10 * x11 * x15 + x0**2 * x1 * x2 * x3**2 * x4 * x6**2 * x8 * x10 * x13 * x15 - x0 * x1 * x3**2 * x4 * x6 * x8**2 * x9 * x10 * x11 * x13 * x15 - x0**2 * x1 * x2 * x3**2 * x4 * x6 * x8**2 * x10 * x15**2 + x0 * x1 * x3**2 * x4 * x6**2 * x8 * x9 * x10 * x11 * x15**2 - x0 * x1**2 * x3**2 * x4 * x6 * x8 * x9 * x10**2 * x11 + x0 * x1**2 * x2 * x3**2 * x4 * x6 * x8 * x10**2 * x13 - x0**2 * x3**2 * x4 * x6**2 * x8**2 * x9 * x11 * x13 + x0**2 * x2 * x3**2 * x4 * x6**2 * x8**2 * x13**2 + x0**2 * x2**2 * x3**2 * x4 * x6 * x8**2 * x14**2 + x0 * x2 * x3**2 * x4 * x6**2 * x8 * x9 * x11 * x14**2 - x0**2 * x3**2 * x4 * x6 * x9**2 * x11**2 * x14**2 - x0 * x2**2 * x3**2 * x4 * x6**2 * x8 * x13 * x14**2 + x0 * x3**2 * x4 * x6**2 * x8**2 * x9 * x11 * x13 * x15 - x0 * x2**2 * x3**2 * x4 * x6 * x8**2 * x14**2 * x15 + x0 * x3**2 * x4 * x6 * x9**2 * x11**2 * x14**2 * x15 + x0**2 * x2 * x3**2 * x4 * x6**2 * x8**2 * x15**2 - x0**2 * x1 * x2 * x3**2 * x4 * x6 * x8**2 * x10 + x0 * x1 * x3**2 * x4 * x6**2 * x8 * x9 * x10 * x11 - x0 * x1 * x2 * x3**2 * x4 * x6**2 * x8 * x10 * x13 - x0**2 * x1 * x4 * x6**2 * x8**2 * x10 * x14**2 - x0 * x1 * x2 * x3**2 * x4 * x6 * x8**2 * x10 * x15 + x0 * x1 * x4 * x6**2 * x8**2 * x10 * x14**2 * x15 + x0**2 * x2 * x3**2 * x4 * x6**2 * x8**2 - x0 * x3**2 * x4 * x6 * x8 * x9 * x11 * x13**2 - x2 * x3**2 * x4 * x6**2 * x8**2 * x14**2 + x0 * x3**2 * x4 * x6 * x8 * x9 * x11 * x14**2 + x0 * x2 * x3**2 * x4 * x6**2 * x8**2 * x15 - x0**2 * x3**2 * x4 * x6 * x8 * x9 * x11 * x15 - x0**2 * x2 * x3**2 * x4 * x6 * x8 * x13 * x15 - x0 * x3**2 * x4 * x6 * x8 * x9 * x11 * x15**2 + x0 * x1 * x4 * x6 * x8 * x10 * x13 * x14**2 - x0 * x3**2 * x4 * x6 * x8 * x9 * x11 + x0 * x2 * x3**2 * x4 * x6 * x8 * x13 - x0**2 * x4 * x6 * x8**2 * x14**2 + x0 * x4 * x6**2 * x8 * x13 * x14**2 + x0 * x4 * x6 * x8**2 * x14**2 * x15
    #     ]
    #     self.runit(A, P, Q, x0)

