from solver.atom import Atom
from solver.solver import Solver
from log import *


def logging():
    pass
    # enable_log(LogTopic.ERROR)
    # enable_log(LogTopic.WARNING)
    # enable_log(LogTopic.INFO)
    # enable_log(LogTopic.DEBUG)
    # enable_log(LogTopic.TRACE)
    # enable_log(LogTopic.STAT)
    # enable_log(LogTopic.PROOF)


def gen_solver(R, method: str = "groebner"):
    return Solver(R, method)


def sp_gb(R, P):
    logging()
    solver = gen_solver(R, 'groebner')
    for p in P:
        if R(p).is_zero():
            continue
        solver.push_clause([Atom(p)])
    rslt = solver.search()
    solver.log_statistics()
    if rslt is False:
        return False
    return solver.get_model()


def sp_el(R, P):
    logging()
    solver = gen_solver(R, 'elim')
    for p in P:
        if R(p).is_zero():
            continue
        solver.push_clause([Atom(R(p))])
    rslt = solver.search()
    solver.log_statistics()
    if rslt is False:
        return False
    return solver.get_model()
