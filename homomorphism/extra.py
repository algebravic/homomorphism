from pysat.card import EncType

def try_options(mval, nval, solver='cadical', encoding=EncType.seqcounter, trace=0):

    prob = problem(mval, nval)
    opts = [ dict(coloring=True, bip=True, cardinality=encoding),
             dict(coloring=True, bip=True, cardinality=None),
             dict(coloring=True, bip=False, cardinality=encoding),
             dict(coloring=True, bip=False, cardinality=None),
             dict(coloring=False, bip=True),
             dict(coloring=False, bip=False)
             ]
    times = []
    for opt in opts:
        mod = prob.model(**opt)
        mod.solve(solver=solver)
        times.append((opt, mod.solve_time))
        if trace > 0:
            print("Model({}, {}) with options {}.  Status={}, Time={}".format(
                mval, nval, opt, mod._status, mod.solve_time))

    return times

def parity_strings(lst):
    """
    Input: 
    lst: a list of words.

    Output:
    Two sets of unordered pairs: (a,b) is even if a and b are labels in a string
    of even distance apart, and similarly for odd
    """
    if not (isinstance(lst, (list, tuple, set, frozenset))
            and all((isinstance(_, str) for _ in lst))):
        raise ValueError("Input must be a collection of strings")

    sets = [set(), set()]

    for elt in lst:
        for ind, fst in enumerate(elt):
            for jind, snd in enumerate(elt[ind + 1:]):
                yield (jind + 1) % 2, tuple(sorted([fst, snd]))
