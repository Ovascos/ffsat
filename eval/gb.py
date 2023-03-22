from sage.all import Ideal, PolynomialRing


def gb_lex(R, P):
    FF = R.base_ring()
    q = len(FF)
    R_lex = PolynomialRing(FF, 'x', len(R.gens()), order='lex')
    P = list(R_lex(p) for p in P)
    fp = [x**q - x for x in R_lex.gens()]
    I = Ideal(P + fp)
    # GB = I.groebner_basis(algorithm='toy:buchberger2')
    GB = I.groebner_basis()
    if 1 in GB:
        return False
    vars = list(R_lex.gens())
    vars.reverse()
    A = {}
    for v in vars:
        Pp = list(filter(lambda p: p.variable() == v, GB))
        if not Pp:
            A[v] = 0
            continue
        possible = set(FF)
        for p in Pp:
            s = p.subs(A)
            if s.is_zero():
                continue
            assert not s.is_constant()
            possible.intersection_update(set(-f[0].constant_coefficient() for f in s.factor() if f[0].degree() == 1))
        assert possible
        A[v] = list(possible)[0]
    return {R(v): a for v, a in A.items()}


def gb(R, P):
    FF = R.base_ring()
    q = len(FF)
    fp = [x ** q - x for x in R.gens()]
    I = Ideal(P + fp)
    return not (1 in I)
