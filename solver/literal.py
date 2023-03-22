# literals are stored as in most solvers as unsigned integer
# the lsb defines the sign of the literal
# 2*n   => positive literal n (sign == False)
# 2*n+1 => negative literal n (sign == True)


def sign(literal: int) -> bool:
    return literal & 1 == 1


def num(literal: int) -> int:
    return literal >> 1


def lit(var: int, negated: bool = False) -> int:
    return (var << 1) + 1 if negated else (var << 1)


def negate(literal: int) -> int:
    return literal ^ 1


def toString(literal: int) -> str:
    sgn = "-" if sign(literal) else ""
    return f"{sgn}{num(literal)}"
