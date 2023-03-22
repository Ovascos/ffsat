from log import *
from solver.solver import init, push, search, cleanup
from sage.all import GF, PolynomialRing

enable_log(LogTopic.TRACE)
enable_log(LogTopic.PROOF)
log(LogTopic.TRACE, "Starting")

# set up F_5[x1,...,x5]
FF = GF(5)
R = PolynomialRing(FF, 'x', 5)
x0, x1, x2, x3, x4 = R.gens()

# initialize the solver
init(R)

# create the clauses
push([x1*x2**2 - x3, x4 - x2], [])
push([], [x4*x1 + x0*x2 - x3**2])

# search returns the model or False
print(search())

# delete the solver
cleanup()
