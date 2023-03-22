from typing import *

from log import log, LogTopic
from explain import *

from .trail import *
from .justification import *
from .literal import *
from .atom import Atom
from .clause import Clause
from .feasible_set import FeasibleSet


class Solver:
    def __init__(self, ring, method: str = "elim", max_conflicts: Optional[int] = None):
        variables = ring.gens()
        # vars of the ring
        self.vars = variables
        # current variables
        self.xk = None
        # clauses
        self.clauses: Set[Clause] = set()
        # watched clauses per (model) variable, stores reference to clauses
        self.watches: Dict = {x: [] for x in variables}
        self.watches.update({None: []})
        # value of the current b_variables
        self.values: List[Optional[bool]] = []
        self.justifications: List[Optional[Justification]] = []
        # assignment level of variables
        self.levels: List[Optional[int]] = []
        # tracking the current level
        self.scope_level = 0
        # current (model) variable assignment
        self.assignment: Dict = {x: None for x in variables}
        # set of feasible values during search
        base_elems = frozenset(ring.base_ring())
        self.feasible: Dict = {x: FeasibleSet(x, base_elems) for x in variables}
        # atom by boolean variable
        self.atoms: List[Atom] = []
        # the trail
        self.trail: Trail = Trail()

        # reverse lookup to avoid duplicated variables
        # TODO check if this is too costly
        self.poly2var = {}

        # stop when there are too many conflicts
        self.conflicts = 0
        self.max_conflicts = max_conflicts

        # set explainer
        if method == "elim":
            self.explain = ExplainElim()
        elif method == "elim_fp":
            self.explain = ExplainElimFp()
        elif method == "groebner":
            self.explain = ExplainGroebner()
        elif method == "groebner_fp":
            self.explain = ExplainGroebnerFp()
        else:
            self.explain = Explain()
            log(LogTopic.ERROR, f"ERROR: invalid explain specified")

    # Create boolean variable for atom
    # returns the variable (not a literal)
    def create_var(self, atom: Atom):
        # assert data structure integrity
        assert len(self.atoms) \
               == len(self.values) \
               == len(self.justifications) \
               == len(self.levels) \
               == len(self.poly2var)

        # check for existing atom
        var = self.poly2var.get(atom)
        if var is None:
            # create new variable
            var = len(self.atoms)
            self.atoms.append(atom)
            self.values.append(None)
            self.levels.append(None)
            self.justifications.append(None)
            self.poly2var[atom] = var
        else:
            log(LogTopic.TRACE, f"existing atom generated {atom}")
        return var

    def new_clause(self, literals: Iterable[int], learned: bool = False):
        literals = sorted(literals, key=lambda a: self.atoms[num(a)])
        return Clause(literals, learned)

    def add_clause(self, clause: Clause):
        top_m = self.top_m_var(clause)
        assert top_m is not None
        if clause not in self.clauses:
            self.clauses.add(clause)
            self.watches[top_m].append(clause)
            # E.g. append newly added clause in front and sort by len of clause
            self.watches[top_m].sort(key=lambda cls: len(cls))
            # self.watches[top_m].sort(key=lambda cls: tuple(self.atoms[num(l)] for l in cls))

    def top_m_var(self, c: Union[Clause, list]):
        return max((self.atoms[num(l)].top_variable() for l in c), default=None)

    def is_satisfied(self) -> bool:
        # all variables were assigned, and all clauses were satisfied.
        sat = all(v is not None for v in self.assignment.values())
        assert not sat or all(self.is_clause_satisfied(c) for c in self.clauses)
        return sat

    def assigned_value(self, literal) -> Optional[bool]:
        val = self.values[num(literal)]
        if val is None:
            return None
        return not val if sign(literal) else val

    def new_stage(self):
        # there is at least one unassigned variable greater than self.xk
        # otherwise, we would be sat
        # TODO turn around this order?
        new_xk = min(v for v in self.vars if v > self.xk)
        assert new_xk > self.xk
        log(LogTopic.TRACE, f"search: selecting new variable {new_xk}")
        self.xk = new_xk
        self.trail.push(TrailElementKind.NEW_STAGE, (lambda: self.undo_new_stage()))

    def undo_new_stage(self):
        # we can't undo the first variable
        # if so, we are unsat
        new_xk = max((v for v in self.vars if v < self.xk), default=None)
        log(LogTopic.TRACE, f"search: undo old variable {new_xk}")
        assert new_xk is not None
        assert new_xk < self.xk
        self.xk = new_xk
        self.assignment[new_xk] = None

    def new_level(self):
        self.scope_level += 1
        self.trail.push(TrailElementKind.NEW_LEVEL, (lambda: self.undo_new_level()))

    def undo_new_level(self):
        self.scope_level -= 1

    def value(self, literal: int):
        val = self.assigned_value(literal)
        if val is not None:
            return val

        n = num(literal)
        s = sign(literal)
        a = self.atoms[n]
        # TODO check if top model variable of a is assigned (might be faster)
        v = a.eval(self.assignment)
        return None if v is None else v != s

    def is_clause_satisfied(self, c: Clause) -> bool:
        return any(self.value(l) for l in c)

    ###### Process clauses ########

    def process_clauses(self, clauses: List[Clause]) -> Optional[Clause]:
        for c in clauses:
            if not self.process_clause(c):
                return c
        return None

    def process_clause(self, c: Clause) -> bool:
        if self.is_clause_satisfied(c):
            return True

        num_undef = 0
        first_undef_literal = 0
        first_undef_set = set()

        for l in c:
            v = self.value(l)
            if v is False:
                continue
            if v is True:
                return True
            assert v is None
            b = num(l)
            a = self.atoms[b]
            F = a.base()
            assert self.xk == a.top_variable()

            feasible: set = a.feasible(self.assignment)
            if sign(l):
                feasible = set(F) - feasible

            log(LogTopic.TRACE, f"resolve: feasible set for literal {self.literals_to_string([l])}")
            if feasible == set(F):
                log(LogTopic.TRACE, "resolve: feasible set is full, found literal")
                self.propagate(l)
                return True

            if not feasible:
                log(LogTopic.TRACE, "resolve: feasible set is empty, skip literal")
                self.propagate(negate(l))
                continue

            fs: FeasibleSet = self.feasible[self.xk]
            xk_set = fs.feasible()
            if feasible.issuperset(xk_set):
                log(LogTopic.TRACE, "resolve: feasible set is superset of current set, found literal")
                self.propagate(l, fs.literals_reduced())  # based on current xk_set literals
                return True

            tmp = feasible.intersection(xk_set)
            if not tmp:
                log(LogTopic.TRACE, "resolve: feasible set is incompatible, skip literal")
                self.propagate(negate(l), fs.literals_reduced())  # based on current xk_set literals
                continue

            if num_undef == 0:
                first_undef_literal = l
                first_undef_set = feasible
            num_undef += 1

        if num_undef == 0:
            return False
        elif num_undef == 1:
            # unit propagation
            self.assign(first_undef_literal, make_justification_clause(c))
            self.update_feasible(first_undef_literal, first_undef_set)
        else:
            self.decide(first_undef_literal)
            self.update_feasible(first_undef_literal, first_undef_set)

        return True

    def propagate(self, literal: int, core: Optional[Iterable[int]] = None):

        # use set() in order to copy the core, as this could be modified later
        core = set(core or [])
        core.add(negate(literal))
        self.assign(literal, make_justification_lazy(core))
        assert self.value(literal) is True

    def assign(self, literal: int, jst: Justification):
        log(LogTopic.TRACE, f"assign: assigning literal ({toString(literal)}) <- {jst}")
        assert self.assigned_value(literal) is None
        n = num(literal)
        self.values[n] = not sign(literal)
        self.levels[n] = self.scope_level
        self.justifications[n] = jst
        self.trail.push(TrailElementKind.ASSIGNMENT, (lambda: self.undo_assign(n)), literal)

    def decide(self, literal: int):
        self.new_level()
        self.assign(literal, make_justification_decision())

    def update_feasible(self, literal: int, feasible: Set):
        assert self.xk is not None
        fs: FeasibleSet = self.feasible[self.xk]
        log(LogTopic.TRACE, f"changed infeasible set of var {self.xk}: {fs.feasible()}")
        fs.push(literal, feasible)
        self.trail.push(TrailElementKind.FEASIBLE_UPDATE, (lambda: fs.pop()), literal)
        assert len(fs.feasible()) > 0
        log(LogTopic.TRACE, f"new infeasible set of var {self.xk}: {fs.feasible()}")

    def undo_assign(self, var: int):
        assert var < len(self.values)
        self.values[var] = None
        self.levels[var] = None
        self.justifications[var] = None

    ###### Trail handling ########

    def undo_until_level(self, new_level: int):
        self.trail.undo_until(lambda: self.scope_level > new_level)
        assert self.scope_level == new_level

    def undo_until_stage(self, new_stage):
        self.trail.undo_until(lambda: self.xk > new_stage)
        assert self.xk == new_stage

    def undo_until_unassigned(self, var: int):
        self.trail.undo_until(lambda: self.values[var] is not None)
        assert self.values[var] is None

    ###### Resolve ########

    def resolve(self, conflict: Clause) -> bool:
        # assert the invariants
        assert len(self.atoms) \
               == len(self.values) \
               == len(self.justifications) \
               == len(self.levels)

        log(LogTopic.DEBUG, f"resolve: Start resolution of clause {conflict}")
        self.conflicts += 1
        log(LogTopic.INFO, f"resolve: xk: {self.xk}, level: {self.scope_level},\n"
                           f"         Current assignment: {self.assignment_to_string()}")

        # one mark for each variable
        mark = [False] * len(self.values)
        # counts the marks at current level/stage
        mark_count = 0
        lemma = []
        mark_count += self.resolve_clause(mark, lemma, conflict)

        while True:
            top = len(self.trail)
            found_decision = False
            while mark_count > 0:
                top -= 1
                t = self.trail[top]
                # we only mark literals that are in the same stage
                assert t.kind != TrailElementKind.NEW_STAGE
                if t.kind == TrailElementKind.ASSIGNMENT:
                    assert t.literal is not None
                    b = num(t.literal)
                    assert b is not None and b < len(mark)
                    if mark[b] is True:
                        mark[b] = False
                        mark_count -= 1
                        jst = self.justifications[b]
                        if jst.type == JustificationType.CLAUSE:
                            mark_count += self.resolve_clause(mark, lemma, jst.clause, b)
                        elif jst.type == JustificationType.LAZY:
                            lazy_clause = self.resolve_lazy_justification(jst, mark)
                            mark_count += self.resolve_clause(mark, lemma, lazy_clause, b)
                        elif jst.type == JustificationType.DECISION:
                            log(LogTopic.TRACE, "resolve: found decision")
                            assert mark_count == 0
                            found_decision = True
                            lemma.append(lit(b, self.values[b] is True))
                        else:
                            # unreachable
                            assert False

            # lemma is an implicating clause after backtracking current scope level
            if found_decision:
                break

            # if lemma only contains literals from previous stages, then we can stop
            if self.top_m_var(lemma) < self.xk:
                break

            # Conflict does not depend on the current decision, and it is still in the current stage.
            assert all(self.value(l) is False for l in lemma)
            assert all(self.assigned_value(l) is False
                       or (self.assigned_value(l) is None and self.atoms[num(l)].top_variable() < self.xk)
                       for l in lemma)
            max_lvl = max((self.levels[num(l)] for l in lemma if self.assigned_value(l) is False), default=0)
            log(LogTopic.TRACE, f"resolve: conflict does not depend on current decision, "
                                f"backtracking to level: {max_lvl}")
            assert max_lvl < self.scope_level
            same_lvl = [l for l in lemma
                        if self.assigned_value(l) is False
                        and self.levels[num(l)] == max_lvl
                        and self.atoms[num(l)].top_variable() == self.xk]
            # bump mark_count as the removed literals are going to be in the current level
            mark_count += len(same_lvl)
            lemma = [l for l in lemma if l not in same_lvl]
            self.undo_until_level(max_lvl)
            assert self.scope_level == max_lvl
            log(LogTopic.TRACE, f"resolve: scope_lvl: {max_lvl}, mark_count: {mark_count}")

        log(LogTopic.TRACE, f"resolve: new lemma: {lemma}")
        log(LogTopic.TRACE, f"resolve: new lemma: {self.literals_to_string(lemma)}")

        if len(lemma) == 0:
            log(LogTopic.TRACE, "empty clause generated")
            return False

        new_clause = self.new_clause(lemma, learned=True)
        if not found_decision:
            # case 1
            log(LogTopic.TRACE, "resolve: case 1")
            max_var = self.top_m_var(lemma)
            assert max_var is not None
            assert max_var < self.xk
            log(LogTopic.TRACE, f"resolve: backtracking to stage {max_var}")
            self.undo_until_stage(max_var)
            assert self.xk == max_var
        else:
            # case 2
            log(LogTopic.TRACE, "resolve: case 2")
            assert self.scope_level >= 1
            assert all(
                self.levels[num(l)] is not None for l in lemma[:-1] if self.atoms[num(l)].top_variable() == self.xk)
            new_level = max((self.levels[num(l)] for l in lemma[:-1] if self.atoms[num(l)].top_variable() == self.xk),
                            default=self.scope_level - 1)
            log(LogTopic.TRACE, f"resolve: backtracking to level {new_level}")
            self.undo_until_level(new_level)

        if conflict != new_clause:
            log(LogTopic.TRACE, f"resolve: learned new clause {new_clause}")
            self.add_clause(new_clause)
        else:
            log(LogTopic.TRACE, "resolve: found decision literal in conflict clause")

        # check if we are still in a conflict
        if not self.process_clause(new_clause):
            return self.resolve(new_clause)

        return True

    # returns the number of marked literals of current scope/level
    def resolve_clause(self, mark: list, lemma: list, clause: Union[Clause, list], var: Optional[int] = None) -> int:
        log(LogTopic.TRACE, f"resolve: processing clause for {toString(var) if var else 'all'} var")
        marked = 0
        for antecedent in clause:
            b = num(antecedent)
            if b == var:
                continue
            log(LogTopic.TRACE, f"resolve: processing antecedent: {toString(antecedent)}")
            a = self.atoms[b]
            if self.assigned_value(antecedent) is None:
                assert self.value(antecedent) is False
                assert self.levels[b] is None
                if not mark[b]:
                    assert a.top_variable() < self.xk
                    log(LogTopic.TRACE, "resolve: literal is unassigned, "
                                        "but false in the current interpretation, adding to lemma")
                    mark[b] = True
                    lemma.append(antecedent)
            else:
                lvl = self.levels[b]
                log(LogTopic.TRACE, f"resolve: lvl: {lvl}, is_marked: {mark[b]}")
                if not mark[b]:
                    mark[b] = True
                    # if same level and same stage
                    if lvl == self.scope_level and a.top_variable() == self.xk:
                        marked += 1
                    else:
                        lemma.append(antecedent)
        return marked

    def literals_to_string(self, literals: List[int]) -> str:
        return ", ".join([f"{self.atoms[num(i)]} {'!=' if sign(i) else '=='} 0" for i in literals])

    def resolve_lazy_justification(self, jst: Justification, mark: list) -> list:
        core = jst.core
        assert core is not None

        poly_p = [self.atoms[num(l)].p for l in core if sign(l) is False]
        poly_n = [self.atoms[num(l)].p for l in core if sign(l) is True]

        vs = {x for a in poly_p for x in a.variables()}.union({x for a in poly_n for x in a.variables()})
        assert self.xk in vs

        # core has just one variable, no quantifier elimination possible, use naive explain approach
        if len(vs) == 1:
            log(LogTopic.WARNING, f"skipped quantifier elimination, naive explain approach for {core}")
            return [negate(l) for l in core]

        log(LogTopic.TRACE, f"Explaining: {self.literals_to_string(core)}")

        pos, neg = self.explain(poly_p, poly_n, self.assignment, self.xk)

        assert len(mark) == len(self.values)
        A = {k: v for k, v in self.assignment.items() if v is not None}
        assert all(not p.subs(A).is_zero() for p in pos) and all(q.subs(A).is_zero() for q in neg)

        lemma = []
        lemma.extend([negate(l) for l in core])
        lemma.extend(map(lambda p: lit(self.create_var(Atom(p)), negated=False), pos))
        lemma.extend(map(lambda p: lit(self.create_var(Atom(p)), negated=True), neg))

        # TODO check explanations (using solver setting)

        # extend marks, as we could have new variables
        new = len(self.values) - len(mark)
        mark += [False] * new
        log(LogTopic.DEBUG, f"justification Lemma: {lemma}")
        return lemma

    ######################
    ###### Search ########
    ######################

    def search(self) -> Optional[bool]:
        self.xk = None
        while True:
            log(LogTopic.DEBUG, f"New search loop - xk: {self.xk}")
            if self.is_satisfied():
                return True
            self.new_stage()
            while True:
                conflict_clause = self.process_clauses(self.watches[self.xk])
                if conflict_clause is None:
                    break
                log(LogTopic.DEBUG, f"conflict: {conflict_clause}")
                if not self.resolve(conflict_clause):
                    return False
                # break when max_conflicts is set and reached
                if self.max_conflicts and self.max_conflicts == self.conflicts:
                    return None
            self.select_witness()

    def select_witness(self):
        fs: FeasibleSet = self.feasible[self.xk]
        witness = fs.feasible_element()
        assert witness is not None
        self.assignment[self.xk] = witness
        log(LogTopic.TRACE, f"select_witness: selecting {self.xk}={witness} out of {len(fs.feasible())}")

    ###### Model handling ########

    def get_model(self) -> Optional[Dict]:
        if self.is_satisfied():
            return self.assignment
        return None

    ###### Debug and Helper methods ########

    def push_clause(self, pos: List[Atom], neg: Optional[List[Atom]] = None):
        neg = neg or []
        literals = set()
        literals.update(map(lambda p: lit(self.create_var(p), negated=False), pos))
        literals.update(map(lambda p: lit(self.create_var(p), negated=True), neg))
        self.add_clause(self.new_clause(literals, learned=False))

    def assignment_to_string(self) -> str:
        sz = len(self.values)
        s = [f"{i}:" + ("T" if self.values[i] is True else "F") for i in range(0, sz) if self.values[i] is not None]
        return ", ".join(s)

    def log_statistics(self):
        log(LogTopic.STAT, f"{self.explain.statistics()}")


##################################################################################


solver: Optional[Solver] = None


def init(ring):
    global solver
    solver = Solver(ring)


def cleanup():
    global solver
    solver = None


def search():
    global solver
    if solver is not None:
        rslt = solver.search()
        return solver.get_model() if rslt else False


def push(pos: List, neg: List):
    global solver
    if solver is not None:
        pos = list(Atom(p) for p in pos)
        neg = list(Atom(p) for p in neg)
        solver.push_clause(pos, neg)


def push_unit(a, sgn: bool = True):
    return push([Atom(a)], []) if sgn else push([], [Atom(a)])
