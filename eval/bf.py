from itertools import product


def bf(R, P):
    FF = R.base_ring()
    vars = R.gens()
    for V in product(FF, repeat=len(vars)):
        A = dict(zip(vars, V))
        if all(p.subs(A).is_zero() for p in P):
            return A
    return False
