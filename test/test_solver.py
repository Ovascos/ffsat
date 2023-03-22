from itertools import product

from test.base import TestBase
from typing import List, Optional
from solver.solver import Solver
from solver.atom import Atom


def print_model(model: dict):
    print("Model:")
    for x, v in model.items():
        print(f"  {x}: {v}")


class TestSolver(TestBase):
    def genSolver(self, method: str = "elim", max_conflicts: Optional[int] = None):
        assert self.FF is not None
        assert self.R is not None
        self.solver = Solver(self.R, method, max_conflicts)

    def assertModel(self, model: dict, variables: set):
        self.assertNotEqual(model, None)
        self.assertSetEqual(variables, set(model.keys()))
        for k in model:
            self.assertNotEqual(model[k], None)

    def checkModel(self, model: dict, clauses: List[List], clauses_neg: Optional[List[List]] = None):
        for c in clauses:
            self.assertTrue(any(a.eval(model) for a in c))
        for c in (clauses_neg or []):
            self.assertFalse(all(a.eval(model) for a in c))

    def checkPolynomials(self, poly: list, poly_neg: Optional[list] = None, sat: bool = True):
        assert self.R is not None
        assert self.solver is not None
        clauses = [[Atom(p)] for p in poly]
        clauses_neg = [[Atom(p)] for p in (poly_neg or [])]
        for c in clauses:
            self.solver.push_clause(c)
        for c in clauses_neg:
            self.solver.push_clause([], c)
        result = self.solver.search()
        self.assertEqual(result, sat)
        self.solver.log_statistics()
        if sat:
            model = self.solver.get_model()
            print_model(model)
            self.assertModel(model, set(self.R.gens()))
            self.checkModel(model, clauses, clauses_neg)


class TestSimple(TestSolver):
    def test_simple_1(self):
        x, y = self.genRing(13, 2)
        self.genSolver()
        c1 = [Atom(x + 1)]
        c2 = [Atom(y + 1)]
        self.solver.push_clause(c1, [])
        self.solver.push_clause(c2, [])
        result = self.solver.search()
        self.assertEqual(result, True)
        self.solver.log_statistics()
        model = self.solver.get_model()
        self.assertModel(model, {x, y})
        self.checkModel(model, [c1, c2])

    def test_simple_2(self):
        x, y = self.genRing(13, 2)
        self.genSolver()
        c1 = [Atom(x + 1), Atom(x + 2)]
        c2 = [Atom(y + 1)]
        self.solver.push_clause(c1, [])
        self.solver.push_clause(c2, [])
        result = self.solver.search()
        self.assertEqual(result, True)
        self.solver.log_statistics()
        model = self.solver.get_model()
        self.assertModel(model, {x, y})
        self.checkModel(model, [c1, c2])

    def test_simple_3(self):
        x, y = self.genRing(13, 2)
        self.genSolver()
        c1 = [Atom(x + 1), Atom(y + 1)]
        self.solver.push_clause(c1, [])
        result = self.solver.search()
        self.assertEqual(result, True)
        self.solver.log_statistics()
        model = self.solver.get_model()
        self.assertModel(model, {x, y})
        self.checkModel(model, [c1])

    def test_simple_4(self):
        x, y = self.genRing(13, 2)
        self.genSolver()
        c1 = [Atom(x + 1)]
        c2 = [Atom(x + 2)]
        self.solver.push_clause(c1, [])
        self.solver.push_clause(c2, [])
        result = self.solver.search()
        self.assertEqual(result, False)
        self.solver.log_statistics()

    def test_simple_5(self):
        x, y = self.genRing(13, 2)
        self.genSolver()
        c1 = [Atom(x + 1), Atom(x + 2)]
        self.solver.push_clause(c1, [])
        result = self.solver.search()
        self.assertEqual(result, True)
        self.solver.log_statistics()
        model = self.solver.get_model()
        self.assertModel(model, {x, y})
        self.checkModel(model, [c1])

    def test_simple_6(self):
        x, y = self.genRing(13, 2)
        self.genSolver()
        c1 = [Atom(x * y + 3)]
        c2 = [Atom(y + 1)]
        self.solver.push_clause(c1, [])
        self.solver.push_clause(c2, [])
        result = self.solver.search()
        self.assertEqual(result, True)
        self.solver.log_statistics()
        model = self.solver.get_model()
        print_model(model)
        self.assertModel(model, {x, y})
        self.checkModel(model, [c1, c2])

    def test_simple_7(self):
        # inverse of simple_6, requires explain function
        x, y = self.genRing(13, 2)
        self.genSolver()
        c1 = [Atom(x * y + 3)]
        c2 = [Atom(x + 1)]
        self.solver.push_clause(c1, [])
        self.solver.push_clause(c2, [])
        result = self.solver.search()
        self.assertEqual(result, True)
        self.solver.log_statistics()
        model = self.solver.get_model()
        print_model(model)
        self.assertModel(model, {x, y})
        self.checkModel(model, [c1, c2])

    def test_simple_8(self):
        x, y = self.genRing(13, 2)
        self.genSolver()
        c1 = [Atom(x * y + 3)]
        c2 = [Atom(x * y + 1)]
        self.solver.push_clause(c1, [])
        self.solver.push_clause(c2, [])
        result = self.solver.search()
        self.assertEqual(result, False)
        self.solver.log_statistics()

    def test_simple_9(self):
        x, y = self.genRing(13, 2)
        self.genSolver()
        c1 = [Atom(x * y + 3)]
        c2 = [Atom(x + 1)]
        c3 = [Atom(x ** 4 + 3)]
        self.solver.push_clause(c1, [])
        self.solver.push_clause(c2, [])
        self.solver.push_clause(c3, [])
        result = self.solver.search()
        self.assertEqual(result, False)
        self.solver.log_statistics()

    def test_simple_10(self):
        x, y = self.genRing(13, 2)
        self.genSolver()
        c1 = [Atom(x - 3), Atom(x - 8)]
        c2 = [Atom(x * y + x ** 2)]
        self.solver.push_clause(c1)
        self.solver.push_clause(c2)
        result = self.solver.search()
        self.assertEqual(result, True)
        self.solver.log_statistics()
        model = self.solver.get_model()
        print_model(model)
        self.assertModel(model, {x, y})
        self.checkModel(model, [c1, c2])


class TestMedium(TestSolver):
    def test_medium_1(self):
        x, y, z, t = self.genRing(5, 4)
        self.genSolver()
        F1 = x ** 2 + t * x ** 2 - z * x - t * z * x + t * z + 3 * z
        F2 = t * x + y - t * z
        G1 = 3 * x ** 2 - 3 * z * x + 6 * t * x - 3 * y * x + 3 * z * y - 6 * t * y
        G2 = 6 * x ** 2 + 15 * t * z * x - 6 * y * x - 15 * t * z * y
        self.checkPolynomials([F1, F2, G1, G2])

    def test_medium_2(self):
        x, y, z, t = self.genRing(7, 4)
        self.genSolver()
        F1 = x ** 2 + t * x ** 2 - z * x - t * z * x + t * z + 3 * z
        F2 = t * x + y - t * z
        G1 = 3 * x ** 2 - 3 * z * x + 6 * t * x - 3 * y * x + 3 * z * y - 6 * t * y
        G2 = 6 * x ** 2 + 15 * t * z * x - 6 * y * x - 15 * t * z * y
        # search for a solution without 0 for x, y, z
        self.checkPolynomials([F1, F2, G1, G2], [x, y, z])

    def test_medium_3(self):
        x, y, z, t = self.genRing(5, 4)
        self.genSolver()
        P1 = x ** 31 - x ** 6 - x - y
        P2 = x ** 8 - z
        P3 = x ** 10 - t
        self.checkPolynomials([P1, P2, P3])

    def test_medium_4(self):
        # example 3.1.1, TODO check var order and original problem
        x, y, z, t = self.genRing(5, 4)
        self.genSolver()
        T1 = z ** 3 - z ** 2 + t ** 2 - 1
        T2 = x ** 4 + z ** 2 * x ** 2 - t ** 2 * x ** 2 + z ** 4 - 2 * z ** 2 + 1
        T3 = x * y + z ** 2 - 1
        self.checkPolynomials([T1, T2, T3])


class TestUnsat(TestSolver):
    def test_unsat_1(self):
        x0, x1, x2, x3, x4 = self.genRing(3, 5)
        self.genSolver()
        P = [x0 ** 2, x0 + 1]
        self.checkPolynomials(P, [], False)

    def test_unsat_2(self):
        x0, x1, x2, x3, x4 = self.genRing(3, 5)
        self.genSolver()
        P = [x3 ** 2, x3 + 1]
        self.checkPolynomials(P, [], False)

    def test_unsat_3(self):
        x0, x1, x2, x3, x4 = self.genRing(3, 5)
        self.genSolver()
        P = [x4 * x1 + 2, x2 + 2 * x1, x0 ** 2, x0 + 1]
        self.checkPolynomials(P, [], False)

    def test_unsat_4(self):
        x0, x1, x2, x3, x4 = self.genRing(3, 5)
        self.genSolver()
        P = [x3 ** 2, x1 * x3 + 1]
        self.checkPolynomials(P, [], False)

    def test_unsat_5(self):
        x0, x1, x2, x3, x4 = self.genRing(3, 5)
        self.genSolver()
        P = [x3 ** 2]
        Q = [x3 + 0, x3 + 1, x3 + 2]
        self.checkPolynomials(P, Q, False)

    def test_unsat_6(self):
        x0, x1, x2, x3, x4 = self.genRing(3, 5)
        self.genSolver()
        P = [x1 * x3 + 1]
        Q = [x1 * x3 + 1]
        self.checkPolynomials(P, Q, False)

    def test_unsat_7(self):
        x0, x1, x2, x3, x4 = self.genRing(3, 5)
        self.genSolver()
        P = [x1 * x3 + 1]
        Q = [x1 * x3 + 1]
        self.checkPolynomials(P, Q, False)

    def test_unsat_8(self):
        x0, x1, x2, x3, x4 = self.genRing(3, 5)
        self.genSolver()
        P = [x0 * x1 * x2 * x3 * x4]
        Q = [x0, x1, x2, x3, x4]
        self.checkPolynomials(P, Q, False)

    def test_neg_9(self):
        x0, x1, x2, x3, x4 = self.genRing(3, 5)
        self.genSolver()
        P = [x0]
        Q = [x0 * x1 * x2 * x3 * x4]
        self.checkPolynomials(P, Q, False)

    def test_neg_10(self):
        x0, x1, x2, x3, x4 = self.genRing(3, 5)
        self.genSolver()
        P = [x0]
        Q = [x0, x1, x2, x3, x4]
        self.checkPolynomials(P, Q, False)


class TestNegate(TestSolver):
    def test_neg_1(self):
        x0, x1, x2, x3, x4 = self.genRing(3, 5)
        self.genSolver()
        P = []
        Q = [x0 ** 2, x1, x2 * x3, x4 + 1]
        self.checkPolynomials(P, Q, True)

    def test_neg_2(self):
        x0, x1, x2, x3, x4 = self.genRing(3, 5)
        self.genSolver()
        P = []
        Q = [x1, x1 + 1, x1 + 2]
        self.checkPolynomials(P, Q, False)

    def test_neg_3(self):
        x0, x1, x2, x3, x4 = self.genRing(3, 5)
        self.genSolver()
        P = []
        Q = [x1 ** 2 - 1]
        self.checkPolynomials(P, Q, True)

    def test_neg_4(self):
        x0, x1, x2, x3, x4 = self.genRing(3, 5)
        self.genSolver()
        P = []
        Q = [x0 * x1 * x2 * x3 * x4]
        self.checkPolynomials(P, Q, True)


class TestEdge(TestSolver):
    def test_edge_1(self):
        self.genRing(3, 5)
        self.genSolver()
        P = []
        Q = []
        self.checkPolynomials(P, Q, True)

    def test_edge_2(self):
        self.genRing(3, 5)
        self.genSolver()
        P = self.R.gens()
        Q = []
        self.checkPolynomials(P, Q, True)

    def test_edge_3(self):
        self.genRing(3, 5)
        self.genSolver()
        P = []
        Q = self.R.gens()
        self.checkPolynomials(P, Q, True)

    def test_edge_4(self):
        self.genRing(3, 5)
        self.genSolver()
        P = self.R.gens()
        Q = self.R.gens()
        self.checkPolynomials(P, Q, False)


class TestBig(TestSolver):
    def test_big_1(self):
        x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16, x17, x18, \
            x19, x20, x21, x22, x23, x24 = self.genRing(3, 25)
        self.genSolver()
        P = [
            -x2 * x20 ** 2 + x21 * x22 * x23 + x7 * x12 * x24,
            -x0 * x17 ** 2 - x14 ** 2 * x18 + x7 * x14 * x19 + x15 * x21 * x23,
            -x0 * x10 ** 2 + x0 * x17 * x18 - x5 * x16 * x19 + x1 * x2,
            -x4 * x12 * x13 - x10 * x13 * x19 - x13 * x15,
            x7 * x8 * x9 + x2 * x15 * x17 - x3 * x12 * x23 - x2 * x7,
            x6 ** 2 * x9 - x15 * x17 * x22 - x8 * x23 ** 2 - x15 ** 2 * x24,
            x1 * x9 * x14 + x4 * x12 * x17 + x1 * x6 * x23 - x12 * x13,
            x8 * x9 * x10 - x0 * x19 ** 2,
            x11 * x15 * x17 - x9 * x18 * x20 - x3 * x4 * x23,
            x5 ** 2 * x9 + x4 * x7 * x11 + x9 * x17 * x21,
            x5 * x12 ** 2 + x6 * x13 ** 2 + x4 * x8 * x16 + x6 * x9 * x19,
        ]
        Q = [
            x1 * x9 * x17 + x8 * x13 * x22 - x15 * x17 * x23 + x16 * x20 * x24,
            -x1 * x6 * x12,
            x3 * x8 * x23 + x1 * x12 * x24,
            x4 * x6 * x21 + x1 * x10 * x22 + x5 * x6 * x24,
            x21 - x2,
            -x3 * x7 * x17 + x1 * x20 * x21 + x2 * x10,
            # -x2 * x7 * x14 + x9 * x12 * x19 - x3 * x20 * x22 - x0 * x3 * x24,
            -x2 * x8 * x10 + x1 * x6 * x16 - x4 * x12 * x17 + x6 * x11 * x20,
            # x1 * x5 * x10 - x5 ** 2 * x10 - x8 ** 2 * x19 + x6 * x10 * x19,
            -x5 * x21 ** 2 + x2 * x8 * x22,
            # -x2 * x5 * x7 + x2 * x6 * x12 + x1 * x2 * x14 + x5 * x6 * x20 - x12 * x20 * x23
        ]
        self.checkPolynomials(P, Q)

    def test_big_2(self):
        x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16, x17, x18, \
            x19, x20, x21, x22, x23, x24 = self.genRing(3, 25)
        self.genSolver()
        P = [
            x0 * x7 * x16 + x9 ** 2 * x19,
            x14 * x15 * x16 + x6 * x16 ** 2 + x5 * x15 * x17 + x10 ** 2 * x20,
            - x7 * x12 * x17 + x16 * x18 ** 2,
            x0 * x10 * x18 - x17 * x20 * x24 + x4 * x12,
            - x9 * x13 * x17 - x6 * x14 * x19 - x1 * x7 * x20 + x1 * x17 * x21,
            x8 * x10 * x14 + x2 * x17 * x18,
            x4 * x23,
            - x1 * x8 * x9 - x6 * x13 * x16 - x17 ** 2 * x23 - x7 * x21,
            - x1 * x12 * x15 + x15 ** 3,
            x12 * x15 * x20 - x7 * x11 * x21,
            - x6 * x10 * x13 + x1 * x13 * x18 + x9 * x20 ** 2 - x14 * x21 * x23,
            x7 * x14 * x15 - x1 * x19 * x20 - x2 ** 2 * x23 - x13 * x14 * x23,
            - x3 * x11 ** 2 + x3 * x5 * x12 + x8 ** 2 * x16 + x14 * x15 * x20,
            x2 ** 2 * x10 - x3 * x9 * x18 + x0 * x21 * x23 - x7 * x21 * x23 + x18 * x20 * x24,
            x3 ** 2 * x4 - x6 * x12 * x14 - x0 * x15 * x18 + x12 * x15 * x24,
            x7 * x9 * x19 + x1 * x11 * x19 + x3 * x14 * x23 - x14 * x20 * x23,
            - x5 * x9 * x11 - x7 * x12 * x16 + x0 * x12 * x17 + x4 * x15 * x19,
            x7 * x17 * x19 - x6 * x20 * x22 - x22 * x23,
            x4 * x10 * x18 - x5 ** 2,
            - x2 * x6 * x17 + x3 * x17 * x23 + x9 * x20,
            - x6 * x7 * x11 + x20 * x24 ** 2 - x2 * x19,
            - x1 * x4 * x8 + x2 * x3 * x9 - x12 * x17 * x24,
            x2 ** 2 * x12 - x1 * x10 * x16 + x15 * x17 * x19 + x14 * x18 * x23,
            - x9 * x13 * x14 + x2 ** 2 * x15 - x9 * x19 * x20 + x15 * x23,
            x2 * x3 * x9 + x5 * x7 * x18 + x2 * x20 * x22 - x0 * x22 ** 2,
        ]
        Q = list(self.R.gens())
        self.checkPolynomials(P, Q, False)

    def test_big_3(self):
        x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16, x17, x18, \
            x19, x20, x21, x22, x23, x24 = self.genRing(3, 25)
        self.genSolver()
        P = [
            x0 * x1 * x2 - x0 * x3 * x4 + x0 * x4 * x5 + x3 * x8 * x9,
            - x6 * x11 ** 2,
            x16 ** 2 * x18 - x13 * x16 * x22 + x15 * x11 ** 2,
            x15 * x22 * x17 - x17 * x11 * x17 - x15 * x20,
            - x15 * x18 ** 2 - x16 * x19 * x17,
            - x6 * x7 ** 2 + x2 * x7 * x10 + x1 * x2 * x11 + x6 * x7,
            x7 ** 2 * x8 - x1 ** 2 * x9 - x0 * x8 * x10 - x5 * x6,
            x1 * x2 * x4 - x0 * x11,
            x0 * x5 ** 2 + x0 * x7 * x10 + x0 * x12 ** 2 - x6 * x12,
            - x1 ** 2 * x10 - x1 * x6 * x10 + x6 * x7,
            x6 * x8 * x9 - x5 ** 2 * x10 - x4 * x5 * x11 - x2 * x7 * x12,
            - x0 * x4 * x12 - x2 * x8 * x12 + x0 * x3 - x6 * x8,
            x1 * x4 ** 2 + x0 * x8 * x10 + x12,
            - x1 ** 2 * x2 - x6 * x10 * x12 - x4 * x11 * x12 - x11 * x12 ** 2,
            - x3 * x6 ** 2 - x0 ** 2 * x7 + x0 * x6 * x10,
            x17 * x14 ** 2 + x13 * x15 * x22 + x14 * x15 * x22 - x17 * x13 * x17,
            x0 ** 2 * x1 + x2 ** 3 - x7 * x10 * x12,
            - x2 * x8 ** 2 + x1 * x3 * x12 - x1 * x11 * x12,
            x1 * x5 * x9 + x1 ** 2 * x11 - x10 ** 2 * x12,
            x1 * x3 * x9 - x2 * x3 * x11 - x9 * x12,
            - x13 ** 2 * x21 + x17 * x21 * x22 + x18 * x11 ** 2 - x15 * x19 * x17,
            x16 ** 2 * x18 - x13 * x16 * x22 + x15 * x11 ** 2,
            x15 * x22 * x17 - x17 * x11 * x17 - x15 * x20,
            - x15 * x18 ** 2 - x16 * x19 * x17,
            - x14 ** 2 * x15 + x18 ** 2 * x22 + x16 * x20 * x22 + x15 * x21 * x17,
            - x13 * x16 ** 2 + 1,
            - x17 * x18 * x21 + x14 * x15 * x11 + x20 * x21 * x11 - x16 * x19 - x20 * x21,
            x13 * x14 * x21 + x13 * x15 * x11 + x15 * x20 * x11,
            x8 * x9 ** 2 + x3 ** 2 * x12 + x3 * x6,
            - x4 * x11 * x12 + x2 * x5,
            x0 ** 2 * x5 + x4 * x5 ** 2 + x5 * x8 * x11 + x3 * x9 * x11 + x2 * x9,
            - x2 * x7 * x9 + x3 * x7 * x10 + x4 * x10 * x11 - x8 ** 2 * x12 + x0 * x7,
            - x3 ** 2 * x5 + x0 * x1 * x7 + x5 * x10 * x11 - x1 * x2,
            x0 * x3 * x4 + x1 * x5 * x6 - x0 * x5 * x8 + x5,
            x1 ** 2 * x8 - x0 * x1 * x10 + x1 * x8 * x11 + x3 * x9,
            x0 * x1 * x2 - x3 * x5 ** 2 + x3 * x5 * x9,
            x5 * x6 * x12 + x0 * x7 * x12 - x8 ** 2 * x12 + x3 * x4,
            -x15 * x18 * x11 + x13 * x19,
            x17 * x15 * x21 + x18 ** 2 * x22 + x14 * x11 ** 2 + x18 * x21 * x17 + x14 * x20,
            - x17 * x16 * x20 - x15 ** 2 * x17 + x14 * x11 * x17,
            - x16 ** 2 * x18 + x17 ** 2,
            x13 * x15 ** 2 + x21 * x17 ** 2 - x15 * x21,
            - x13 ** 2 * x21 + x17 * x21 * x22 + x18 * x11 ** 2 - x15 * x19 * x17,
            x16 ** 2 * x18 - x13 * x16 * x22 + x15 * x11 ** 2,
            x15 * x22 * x17 - x17 * x11 * x17 - x15 * x20,
            - x15 * x18 ** 2 - x16 * x19 * x17,
            - x14 ** 2 * x15 + x18 ** 2 * x22 + x16 * x20 * x22 + x15 * x21 * x17,
            - x13 * x16 ** 2,
            - x17 * x18 * x21 + x14 * x15 * x11 + x20 * x21 * x11 - x16 * x19 - x20 * x21,
            x13 * x14 * x21 + x13 * x15 * x11 + x15 * x20 * x11,
            x13 ** 2 * x15 - x15 * x15 * x19 - x19 ** 2 * x20 - x13 * x20 * x21 - x14 * x22 * x17,
            x13 * x20 ** 2 - x15 * x17 ** 2 + x18 * x11,
            x13 * x14 * x19 + x17 * x17 ** 2 - x15,
            - x14 ** 2 * x16 - x17 * x14 * x22 - x17 ** 2,
            - x14 * x15 ** 2 + x18 ** 2 * x22 + x17 * x20 * x22 - x13 * x19,
            - x17 * x13 * x18 + x17 * x18 * x21 - x17 * x21,
            - x15 * x18 * x20 + x21 * x22 ** 2 + x13 ** 2,
            x17 * x14 ** 2 + x13 * x15 * x22 + x14 * x15 * x22 - x17 * x13 * x17,
            x16 * x19 * x22 - x19 * x20 * x22 - x14 * x21 * x22 - x13 * x11 * x17 - x17 * x16,
            x15 ** 3 + x14 * x19 * x22 - x13 * x21 * x11 + x15 * x11 ** 2 + x14 * x21,
            x14 * x11 ** 2 - x16 * x15 * x17 + x14 * x22 + 2,
            x13 ** 3 - x18 ** 2 * x17 - x17 * x15,
        ]
        Q = list(self.R.gens())
#        Q = []
        self.checkPolynomials(P, Q, False)

    def test_big_4(self):
        x0, x1, x2, x3, x4, x5, x6, x7, x8, x9 = self.genRing(3, 10)
        self.genSolver()
        P = [x0*x2*x3 - x0*x6*x9 - x6*x7*x9,
             -x0*x1*x6 + x0*x2*x7 + x4**2*x9,
             -x0*x3*x5 + x0*x3*x6 + x0*x8,
             -x0*x6 + x1*x4 - x3*x6*x7 + x3*x8 + x5*x6,
             x0*x2*x8 - x0*x2 - x3*x4*x9,
             x0**2*x6 - x0*x6*x8 - x2*x4*x7 - x2*x5*x8 + x2*x8*x9,
             -x0**2*x5 - x0*x6**2 - x2*x7*x9,
             x1*x3 + x2*x6*x9 + x3,
             x1*x2 + x1*x6*x8 - x2*x4*x9 + x2*x7**2 - x5**2*x8,
             -x0*x3 + x1*x3 - x1*x7*x8,
             x0*x3 + x1*x5*x9,
             -x0*x3**2 + x2**3 - x3**2*x4 + x4**2*x6,
             -x1*x2*x9,
             -x0**2*x3 + x0,
             x3*x6*x8,
             -x1*x7 - x4*x6**2 + x5**2*x8 - x7*x8**2,
             x0*x4*x8 - x1*x5*x9 - x4*x6**2,
             -x0**2*x4 - x1*x2*x3 + x3*x8*x9,
             x2**2*x6 + x3**2*x5 - x3*x4*x8,
             x0*x8 - x1*x2*x8,
             -x0*x2*x6 - x0*x2 + x1 - x4*x8**2,
             -x1*x2*x9 + x2*x3 + x3*x4*x5,
             x3**2*x4 + x4**2 - x6*x7*x9]
        Q = [x5, x7, x8]
        self.checkPolynomials(P, Q, False)


class TestReference(TestSolver):
    def test_ssys_p1_inv(self):
        x1, x2, x3, x4, x5 = self.genRing(5, 5)
        self.genSolver()
        P = [
            x1*(x1-2)**6,
            x2**2*(x2-1),
            (x3-1)**2*(x3-2)**3,
            (x4-1)*(x4-2)**5,
            ((x1-1)*x5**6 + x1*x2*x5**2 + (x1-2)*(x2-1)*(x3-1)*x4*x5**3 + 1)*(x5+x4+x3)
        ]
        self.checkPolynomials(P)

    def test_ssys_p1(self):
        x5, x4, x3, x2, x1 = self.genRing(5, 5)
        self.genSolver()
        P = [
            x1*(x1-2)**6,
            x2**2*(x2-1),
            (x3-1)**2*(x3-2)**3,
            (x4-1)*(x4-2)**5,
            ((x1-1)*x5**6 + x1*x2*x5**2 + (x1-2)*(x2-1)*(x3-1)*x4*x5**3 + 1)*(x5+x4+x3)
        ]
        self.checkPolynomials(P)

    def test_ssys_p2(self):
        x5, x4, x3, x2, x1 = self.genRing(5, 5)
        self.genSolver()
        P = [
            x1**5*(x1+1)**17*(x1+2)**9,
            (x1**2+x1+1)*x2**5+(2*x1**3+3)*x2+3,
            ((x1**4+x2)*x3+x2)**5*((x2+1)*x3**5+(x1+x3)*x3**2+1)**7,
            (x4**11+2*x4+4)**11*(x4+3)**23,
            (x1+x2+x3)*x5**3 + (x1+x2)*x5 + (x3+x4)
        ]
        self.checkPolynomials(P)

    def test_ssys_p2_inv(self):
        x1, x2, x3, x4, x5 = self.genRing(5, 5)
        self.genSolver()
        P = [
            x1**5*(x1+1)**17*(x1+2)**9,
            (x1**2+x1+1)*x2**5+(2*x1**3+3)*x2+3,
            ((x1**4+x2)*x3+x2)**5*((x2+1)*x3**5+(x1+x3)*x3**2+1)**7,
            (x4**11+2*x4+4)**11*(x4+3)**23,
            (x1+x2+x3)*x5**3 + (x1+x2)*x5 + (x3+x4)
        ]
        self.checkPolynomials(P)

    def test_ssys_p4(self):
        x5, x4, x3, x2, x1 = self.genRing(5, 5)
        self.genSolver()
        P = [
            (x1**4+4*x1**2+3*x1+1)*(x1**5+4*x1+2)*(x1+3)**15,
            (x2**4+x2**2+2)**2*(x2**3+x2+4)**10,
            (x3**2+x3+2)**3*(x3**3+x3**2+x3)**15,
            (x4-2)**5*(x4-1),
            ((x1-x2)*x5+1)**2*(x5+x4+x3)
        ]
        self.checkPolynomials(P, sat=False)

    def test_ssys_p4_inv(self):
        x1, x2, x3, x4, x5 = self.genRing(5, 5)
        self.genSolver()
        P = [
            (x1**4+4*x1**2+3*x1+1)*(x1**5+4*x1+2)*(x1+3)**15,
            (x2**4+x2**2+2)**2*(x2**3+x2+4)**10,
            (x3**2+x3+2)**3*(x3**3+x3**2+x3)**15,
            (x4-2)**5*(x4-1),
            ((x1-x2)*x5+1)**2*(x5+x4+x3)
        ]
        self.checkPolynomials(P, sat=False)

    def test_ssys_p7(self):
        x5, x4, x3, x2, x1 = self.genRing(541, 5)
        self.genSolver()
        P = [
            x1*(x1-2)**5,
            x2**2*(x2**3+4*x2**3+3*x2+1)*(x2**4+3*x2**2+3)**3,
            (x3**4+4*x3**2+3*x3+1)*(x3**3+x3**2+1)**2*(x3-2)**3,
            (x4-2)**5*(x4**5+2*x4**3+3*x4**2+x4+4)*(x4**4+3*x4*2+x4+1)**3,
            (x1-1)*x5**15+(x4+x1)*x5**10
        ]
        self.checkPolynomials(P)

    def test_ssys_p7_inv(self):
        x1, x2, x3, x4, x5 = self.genRing(541, 5)
        self.genSolver()
        P = [
            x1*(x1-2)**5,
            x2**2*(x2**3+4*x2**3+3*x2+1)*(x2**4+3*x2**2+3)**3,
            (x3**4+4*x3**2+3*x3+1)*(x3**3+x3**2+1)**2*(x3-2)**3,
            (x4-2)**5*(x4**5+2*x4**3+3*x4**2+x4+4)*(x4**4+3*x4*2+x4+1)**3,
            (x1-1)*x5**15+(x4+x1)*x5**10
        ]
        self.checkPolynomials(P)


class TestGenUnsat(TestSolver):
    def test_gen_unsat_1(self):
        x0, x1, x2, x3, x4 = self.genRing(3, 5)
        self.genSolver()
        P = [-x1 * x2 + x2 - x4,
             -x2 ** 2 - x0 * x3 + x2 * x4 + x3 * x4,
             x1 * x2 - x1 * x3 + x3,
             x2 * x3 - x3 ** 2 - x4 ** 2 + x2 - x4,
             x0 * x2 - x1 * x4,
             -x1 ** 2 - x1 * x4 + x2 + x3,
             -x1 ** 2 - x2 ** 2 - x0 * x3 - x1 * x3 + x0,
             x2 ** 2 + x1 * x3 - x0 - x1,
             x2 ** 2 - x2 * x4 - x4,
             -x0 * x1 - x3 ** 2 + 1]
        self.checkPolynomials(P, [], False)

    def test_gen_unsat_2(self):
        x0, x1, x2, x3, x4 = self.genRing(3, 5)
        self.genSolver()
        P = [-x2 * x3 - x0 * x4 - x2 * x4,
             x1 * x2 + x4 ** 2 + x4,
             x0 * x1 + x1 * x3,
             x0 * x1 - x1 * x2 + x0 * x4 - x2,
             x0 * x1 - x2 ** 2 - x4 ** 2,
             -x1 * x3,
             -x0 * x3 - x0 * x4 - x1 - x4,
             x0 * x2,
             -x1 ** 2 + x1 * x2 + x4 ** 2 - 1]
        self.checkPolynomials(P, [], False)
