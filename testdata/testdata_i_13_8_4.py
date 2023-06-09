# testdata_13_8_4
# fs = 13
# vc = 8
# f = 1.1
# pc = 4
# tc = 25
def setting():
    return 13, 8


def data(R):
    x0, x1, x2, x3, x4, x5, x6, x7,  = R.gens()
    return [
        [
            6*x3*x4**2 + 4*x0*x3*x5 - 6*x1*x5**2 + 2*x4*x7 - 2*x4,
            6*x1**2*x2 - 6*x4**2*x7 + 6*x0*x6*x7 - 4*x4*x6 - 2*x5*x6,
            -4*x1**2*x2 + x3**2*x4 - 2*x0*x2*x5 - 3*x0**2*x6 + 4*x1*x3*x7 - 4,
            5*x1*x2*x4 + 5*x1*x4*x6 + x2*x4*x6 + 5*x4*x6**2 + 6*x2*x4,
        ],
        [
            -2*x1*x2*x4 - 3*x7**3 - 6*x0**2 + 4*x5**2 - 5*x4,
            4*x4**3 - 4*x2*x7 + 4*x7,
            x0**2*x6 - 4*x1*x5*x6 - 4*x1*x4*x7,
            -2*x0*x1*x3 - x0*x4*x6 - 6*x1**2*x7 + 2*x4*x5*x7,
        ],
        [
            x0*x1*x5 + 5*x2*x5**2 + 2*x1*x5*x7 + 4*x2,
            5*x0*x1**2 - 3*x0**2*x2 - 2*x1*x2*x3 + x0*x4*x5 - 3*x1*x5*x7,
            6*x1**2 + x0*x2 + x7 - 6,
            -4*x0*x2*x3 + x2*x3*x4 + 3*x1*x4*x6 + 5*x3*x6 + x6,
        ],
        [
            4*x3**3 - 3*x2**2*x4 - 6*x0*x3*x4 + x1*x2*x5 - 6*x2*x4,
            -2*x2**3 - 3*x1*x4*x7 + x4**2 - 2*x7,
            -6*x2**3 + 2*x2*x3**2 - 5*x5*x6**2 - 3*x0*x2*x7 + 3*x3*x4,
            -6*x1*x2*x4 - x1*x4*x5 + x0*x3*x7 + 2*x0*x6*x7 + 6,
        ],
        [
            6*x1*x4*x7 + 3*x7**3 - 5*x3*x5 - 4*x4*x5 + x6,
            -3*x1*x2*x3 + x3*x4*x6 - 5*x2*x6**2 - 3*x1*x6*x7 - 12,
            -x0**2*x4 - 5*x4**3 + 2*x1*x5*x7 + x3*x7**2 - 4*x1*x4,
            -x1**3 - 3*x0*x3**2 - 6*x0**2*x7 - 5*x0*x5*x7 - 4*x0*x2,
        ],
        [
            2*x0*x1*x5 - x1*x4*x6 + 4*x1*x4*x7 + 6*x1*x4 - 6*x0,
            -3*x1**2*x3 + 2*x4*x5**2 - 5*x2**2 + 4*x3*x5,
            -4*x1*x2*x3 - 4*x2**2*x3 - 2*x2*x7 + x3*x7 + 2*x5,
            -2*x0*x1*x4 + 2*x0*x4**2 + 3*x1*x3*x7 - 4*x0*x6*x7 + 5*x2*x3,
        ],
        [
            -5*x0*x1*x5 - 3*x3*x5**2 + 6*x4*x5**2 - 6*x2*x5*x7 + 5*x0*x6,
            2*x0*x1**2 + 5*x3*x4*x6 - 2*x4*x5*x7 + x2*x6*x7 + 6,
            3*x1*x4**2 - 2*x3*x4*x7 - x3*x5*x7 - x4*x5*x7 + 6*x1**2,
            4*x0**2*x1 + 2*x1**3 + 4*x0*x2*x6 + 5*x1*x3 - x0*x4,
        ],
        [
            -x0**2*x5 + 5*x3*x5*x6 - 3*x5**2*x7 - x3*x7,
            -x2*x4**2 - x2*x5**2 - 4*x4*x5**2 - 2*x0*x2*x6 + 3*x1,
            x0**2*x2 + x2**2*x7 + x0*x1 - x2*x6,
            -2*x1**2*x2 + 6*x1*x3*x6 + 5*x4**2*x7 + 6*x1*x7**2 + 5*x2*x7**2,
        ],
        [
            2*x0*x2*x3 + 4*x2*x3*x7 - 2*x0*x4*x7 - 5*x4**2*x7 - 5*x5*x6,
            -4*x0**2*x3 + 4*x3**2*x6 - 5*x5**2,
            -4*x0*x2*x5 + 4*x0*x4*x5 + x4*x5*x7 + 2*x1*x3 + 2*x3,
            5*x1**2*x4 + 6*x1*x2*x6 - 5*x3**2*x7 - 2*x4*x6*x7 - 6*x1*x5,
        ],
        [
            4*x0*x3*x5 - 5*x1*x5**2 - 2*x2*x5*x7 + 6*x1**2 + 6*x2*x5,
            4*x0*x2*x5 + x3*x4*x5 + x2*x3*x7,
            6*x1**2*x2 - x2*x3*x6 + 6*x3**2 + 4*x0*x6 + x2*x7 + 14,
            4*x0*x3*x4 - 2*x2*x4*x7 - 3*x4*x7**2 - 3*x3*x6,
        ],
        [
            5*x0*x1*x3 - 2*x1**2*x4 + x3*x5*x7 - 3*x1*x5 - 6*x5 + 1,
            -3*x0*x1*x2 + 6*x2*x3*x4 + x1*x4**2 + 3*x3*x4**2 + 5*x4*x7**2,
            2*x1**2*x3 + 5*x0*x5**2 + 6*x3*x4*x6 + 5*x3*x5*x6 - 5*x4*x5*x6,
            -x0**2*x1 - 3*x0*x1*x4 - 4*x4*x5*x6 - 4*x0**2*x7 - 2*x6**2*x7 + 8,
        ],
        [
            -6*x1*x4*x7 + 5*x3*x4*x7 - 2*x3**2 - 2*x6,
            4*x0*x3*x4 + 4*x2*x5**2 + 2*x2*x5*x6 - 2*x2*x4*x7 + 4*x4**2 - 3,
            2*x4**3 - 3*x1*x4*x5 + 5*x2*x4*x7 + 5*x0*x6*x7 + 2*x2**2,
            4*x1*x2*x3 + 6*x2*x4**2 - 5*x0*x4*x6 + 2*x0*x4*x7 + 3*x3 + 3,
        ],
        [
            -5*x0*x4*x6 + 2*x4*x5*x7 + x3*x4 + 6*x4*x6,
            -3*x0*x6**2 - 2*x3*x6**2 + 5*x3**2 - 2*x5*x6 - 3*x6**2,
            -5*x1**2*x5 + 4*x1*x7**2 + 4*x1*x4 + 4*x5**2 - x6**2 + 1,
            x2*x3*x5 + 3*x4**2*x6 + 2*x1*x6**2 - 2*x1*x2*x7 - 2*x1*x4*x7,
        ],
        [
            -3*x1*x4**2 - x0*x4*x5 + 2*x3**2*x7 + 4*x0*x4,
            x2*x3*x4 + 3*x4**2*x5 - 2*x5**2*x6 + 4*x2*x3*x7 - 6*x2*x7,
            -3*x1**2*x4 - 6*x3*x4*x5 - 3*x0*x2 - 2*x2**2 - 8,
            -6*x1*x2*x5 - 4*x1**2*x6 - 2*x2**2*x6 - 2*x2*x5*x6 - 6*x0*x2,
        ],
        [
            -2*x0*x6**2 - x1*x5*x7 - 5*x3*x6*x7 + 5*x0,
            -x0*x1*x5 + 2*x3*x4*x5 + 4*x3*x5**2 - 3*x3*x4*x7 + 3*x3*x4 + 6,
            -4*x3**2*x5 - 2*x0*x4*x5 - 5*x2*x5**2 - 3*x4*x6**2 - 4*x4*x7**2,
            -x0**2*x2 + 2*x2*x5**2 + 5*x3*x6*x7 - 6*x0**2 + 3*x1*x2 - 8,
        ],
        [
            4*x0*x1*x4 + 6*x1**2*x5 - 5*x1*x4*x6 + 5*x3**2*x7 + 4*x3*x7,
            -6*x2**3 - x2**2*x3 - 6*x2*x5*x7 + 6*x0*x4 - 2,
            -4*x0*x4**2 + 3*x0*x1*x6 - 6*x2**2*x6 - 3*x4,
            -2*x1*x2*x4 + 3*x2*x3*x7 - 5*x3*x4*x7 + 4*x4*x5 + 4*x0*x7,
        ],
        [
            -4*x0*x3**2 + 4*x3**3 + 6*x2*x5**2 - 6*x4**2*x7,
            6*x0*x1*x2 + 2*x2*x5**2 + 4*x1*x5*x6 - x3*x7**2 + 2*x4,
            5*x0**2*x2 - x1*x5*x7 - 4*x1**2 + 3*x0*x4 - 6*x3*x5,
            6*x1*x3*x4 + 3*x2*x4*x5 - 6*x0*x6*x7 - 5*x1*x3 + 4,
        ],
        [
            6*x2*x4**2 - 5*x0*x3*x7 + 3*x4**2*x7,
            -6*x0*x5**2 + 5*x4**2*x6 + x0*x6**2 - 5*x2*x3 - 9,
            3*x0**2*x4 + 2*x3*x4*x7 + x4**2*x7 - 4*x3*x4 + x4*x6,
            -6*x0*x1*x5 - 3*x0*x2*x5 - 5*x2*x3*x6 - x3**2 + x1*x6,
        ],
        [
            -6*x5**2*x6 - x2*x4*x7 + 2*x4*x6*x7 - 6*x3**2,
            5*x1**2*x4 - 4*x2**2*x7 + 2*x0*x4 + 6*x5**2 + 6*x2*x6,
            -5*x0**2*x1 + 5*x0**2*x3 + 4*x1*x4**2 + 3*x0*x6 + 10,
            -3*x0*x5**2 + 4*x0*x2*x6 + x4*x5*x6 - x1*x3*x7 + 4*x2**2 + 10,
        ],
        [
            -x0*x1**2 + 4*x0*x2*x3 - 6*x0**2*x5 + x2*x3*x5 - 3*x0**2*x6,
            5*x2**2*x4 + 6*x1*x6**2 + 5*x0*x3*x7 + 4*x1*x6 + 11,
            -4*x0*x1*x2 - 3*x0*x2*x3 + 6*x0*x5**2 - x4*x5**2 + 6*x0*x4,
            6*x3*x4**2 + 6*x2*x5*x7 - 5*x1*x6*x7 + 6*x4,
        ],
        [
            -6*x3*x5**2 + 2*x1*x5*x6 + 3*x3*x5*x7 + 2*x6**2,
            -4*x0*x4**2 - x3*x4*x5 - 4*x1*x6**2 - 2*x5*x6**2 - x7,
            -3*x3**2*x5 + 5*x2*x4*x7 - 4*x1*x7**2 + x7**3 + 6*x6,
            -5*x0*x1*x3 - x2*x7**2 - 3*x2*x7 - 5*x7 - 2,
        ],
        [
            6*x2*x3*x5 - x3*x5**2 + 4*x1*x2*x6 + 3*x0*x3*x7 - x3*x4,
            -2*x3**3 - 6*x1*x5*x6 - 5*x1*x2*x7 + 2*x6*x7 + 4*x3,
            2*x0*x1*x3 - 2*x3*x4**2 + 5*x1*x2*x5 - x3*x5 + 3,
            3*x0**2*x3 - 6*x4**2*x5 + 4*x2*x6**2 + x3*x6**2,
        ],
        [
            -4*x1*x2*x3 - 6*x3*x6*x7 + 3*x0*x7**2 - 3*x0*x4 - 3*x0*x5,
            x2*x3**2 + x0*x2*x5 - 6*x2*x7**2 + 3*x1*x2 + 5*x6,
            4*x1**2*x7 + 4*x1*x3*x7 + 4*x2*x4*x7 - x5**2 + x1*x6,
            x2**3 - 6*x1*x5**2 + 6*x1*x4*x6 + 4*x2*x5*x7 + 6*x6 + 3,
        ],
        [
            -3*x2*x5**2 + 2*x0*x5*x7 - 6*x2*x5*x7 - 6*x3*x4 - 4*x4*x7 + 1,
            6*x5**2*x6 + 6*x3*x6**2 - x5*x6**2 - 6*x0*x2*x7 + 3*x2*x4*x7 + 1,
            -4*x1*x2*x5 + 4*x1*x2*x7 + 6*x2*x7**2 + x6**2 + 1,
            x5**2*x6 + 4*x1*x6*x7 + x2**2 - 6*x0*x3 + 2*x3*x5 + 1,
        ],
        [
            -5*x1**3 + 6*x2*x5*x7 - 6*x0*x2 - 3*x1*x4 - x2*x7,
            -3*x5*x6**2 - 3*x0*x5*x7 - 2*x4*x7**2 - x4 + 2,
            -3*x0**2*x4 - 6*x0*x1*x5 + 5*x0*x3*x7 - x0*x3 + 2*x0*x7,
            -5*x0*x4**2 - 4*x0*x4*x5 + 6*x4**2*x7,
        ],
    ]
