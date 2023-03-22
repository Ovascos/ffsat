from test.base import TestBase
from helper import check_ass, check_ass_multi


class TestMisc(TestBase):
    def test_check_ass_1(self):
        x, y, z = self.genRing(13, 3)
        F = [6 * x ** 2 * z ** 3 + 4 * x * y * z ** 3 - x * y + 5,
             -5 * x ** 4 * y - x ** 2 * y ** 3 + 3 * y ** 3 * z ** 2 - 4 * x * y * z]
        A = {y: 7, z: 2}
        self.assertFalse(check_ass(F, [], A, x))

    def test_check_ass_2(self):
        x, y, z = self.genRing(13, 3)
        F = [-x * z ** 4 - 2 * x ** 4 - x ** 2 * y ** 2 + 6 * y ** 3 + 6 * x ** 2 * z,
             -5 * x ** 2 * y ** 3 - 5 * x ** 4 + 3 * x ** 3 * z - 2 * y ** 3 - y ** 2]
        A = {y: 2, z: 1}
        self.assertTrue(check_ass(F, [], A, x))

    def test_check_ass_multi_1(self):
        x, y, z, t = self.genRing(13, 4)
        F = [-5 * x ** 3 * y * z + 2 * x ** 2 * y ** 2 * t - 3 * x * z ** 2 * t + 4 * t ** 4 - 5 * x * t ** 2,
             -6 * x ** 4 * y - 6 * x * y * z ** 2 * t + 6 * x * y * z ** 2 + 2 * t ** 3]
        A = {z: 2, t: 1}
        self.assertTrue(check_ass_multi(F, [], A, [x, y]))

    def test_check_ass_multi_2(self):
        x, y, z, t = self.genRing(13, 4)
        F = [-5 * x ** 3 * y * z + 2 * x ** 2 * y ** 2 * t - 3 * x * z ** 2 * t + 4 * t ** 4 - 5 * x * t ** 2,
             -6 * x ** 4 * y - 6 * x * y * z ** 2 * t + 6 * x * y * z ** 2 + 2 * t ** 3]
        A = {z: 7, t: 6}
        self.assertFalse(check_ass_multi(F, [], A, [x, y]))
