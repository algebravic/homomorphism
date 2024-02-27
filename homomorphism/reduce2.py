""" Reduce the 2-clauses """
from typing import List, Tuple, Dict, Set
import networkx as nx

CLAUSE = List[int]
FORMULA = List[CLAUSE]

def unit_step(formula: FORMULA, verbose: int = 0) -> Tuple[FORMULA, Set[int]]:

    units = set((_[0] for _ in formula if len(_) == 1))
    neg_units = set((-_ for _ in units))
    # Check for UNSAT
    if len(set(map(abs, units))) < len(units):
        if verbose > 0:
            print("UNSAT in unit_step")
        return [[]], units
    if len(units) == 0:
        return formula, set()
    new_formula = set()
    for clause in formula:
        if len(clause) > 1:
            reduced_clause = frozenset(clause).difference(neg_units)
            if len(reduced_clause.intersection(units)) == 0:
                new_formula.add(reduced_clause)
    return list(map(list, new_formula)), units

def unit_propagation(formula: FORMULA, verbose: int = 0) -> Tuple[FORMULA, Set[int]]:

    units = set()
    pass_no = 0
    while True:
        pass_no += 1
        formula, new_units = unit_step(formula)
        if verbose > 0:
            print(f"Pass {pass_no}, # new units = {len(new_units)}")
        if len(new_units) == 0 or formula == [[]]:
            return formula, units
        units.update(new_units)
            
def reduction_step(formula: FORMULA, verbose: int = 0) -> Tuple[FORMULA, Dict[int, int]]:

    """ Reduce a formula """
    gph = nx.DiGraph()
    for clause in (_ for _ in formula if len(_) == 2):
        gph.add_edge(-clause[0], clause[1])
        gph.add_edge(-clause[1], clause[0])

    rewrite = {}
    components = nx.strongly_connected_components(gph)
    is_reduction = False
    comp_no = 0
    for bag in components:
        comp_no += 1
        if verbose > 0:
            print(f"Component {comp_no}: # = {len(bag)}")
        # Find a representative
        # Test for UNSAT
        if len(set(map(abs, bag))) < len(bag): # UNSAT
            # a literal and its negation are equivalent
            return [[]], {}
        if len(bag) > 1:
            is_reduction = True
        representative = min(bag)
        rewrite.update({_:representative for _ in bag})
    # It seems that networkx doesn't give you the reduced graph!
    if not is_reduction: # If no reduction, indicate it by empty rewrite
        return formula, {}
    new_formula = set()
    for clause in formula:
        new_clause = frozenset(rewrite.get(_, _) for _ in clause)
        # Test for tautology
        if len(set(map(abs, new_clause))) == len(new_clause): # Not tautology
            new_formula.add(new_clause)
    
    return list(map(list, new_formula)), rewrite

def two_reduction(formula: FORMULA,
                  verbose: int = 0) -> Tuple[FORMULA, Set[int], Dict[int, int]]:

    units = set()
    rewrite = {}
    pass_no = 0
    while True:
        pass_no += 1
        if verbose > 0:
            print(f"Pass {pass_no}")
        changed = False
        formula, new_units = unit_propagation(formula, verbose = verbose)
        if verbose > 0:
            print(f"# new units = {len(new_units)}")
        changed = changed or len(new_units) > 0
        units.update(new_units)
        formula, rewritten = reduction_step(formula, verbose = verbose)
        if verbose > 0:
            print(f"# new rewrites = {len(rewritten)}")
        changed = changed or len(rewritten) > 0
        rewrite.update(rewritten)
        if not changed:
            return formula, units, rewrite
