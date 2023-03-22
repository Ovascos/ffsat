import random
from sage.all import GF, PolynomialRing


def gen(R, count, factor: float):
    P = []
    FF = R.base()
    for _ in range(count):
        if random.random() < factor:
            p = R.random_element(3) + (FF.random_element() if random.random() < 0.25 else 0)
        else:
            vars = random.sample(R.gens(), random.randint(1, 5))
            p = 1
            for v in vars:
                vals = random.sample(list(R.base_ring()), random.randint(1, 3))
                for val in vals:
                    p = p * (v - val)
        P.append(p)
    return P


if __name__ == '__main__':
    # field size
    fs = 3
    # variable count
    vc = 8
    # irreducible factor
    f = 1.1
    # polynomial count
    pc = 8
    # test case count
    tc = 25

    print(f"# testdata_{fs}_{vc}_{pc}")
    print(f"# fs = {fs}\n# vc = {vc}\n# f = {f}\n# pc = {pc}\n# tc = {tc}")
    print(f"def setting():\n    return {fs}, {vc}\n\n")
    print(f"def data(R):")

    FF = GF(fs)
    R = PolynomialRing(FF, vc, 'x')
    s = "    "
    for i in range(0, vc):
        s += f"x{i}, "
    print(f"{s} = R.gens()")
    print('    return [')
    for _ in range(tc):
        print('        [')
        P = gen(R, pc, f)
        for p in P:
            s = f"            {p},"
            s = s.replace('^', '**')
            print(s)
        print('        ],')
    print('    ]')

