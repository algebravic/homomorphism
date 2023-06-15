import networkx as nx
from .sat_homomorphism import LabeledHomomorphism
import numpy as np
from itertools import product, combinations
from collections import Counter
from pysat.card import EncType
# from .utility import export

PLANETS = ['mercury', 'venus', 'earth', 'mars', 'jupiter', 'saturn', 'uranus', 'neptune', 'pluto']
MONTHS = ['january', 'february', 'march', 'april', 'may', 'june', 'july', 'august', 'september', 'october', 'november', 'december']

LISTS = dict(planets=PLANETS, months=MONTHS)

INTS = (int, np.int8, np.int16, np.int32, np.int64)

def word_graph(word: str) -> nx.Graph:
    """
    word: a string
    """
    if not isinstance(word, str):
        raise ValueError("input {} must be a string".format(word))

    gph = nx.Graph()
    for ind, val in enumerate(word):
        gph.add_node(ind, label=val)
    for ind in range(len(word) - 1):
        gph.add_edge(ind, ind + 1)
    return gph

# @export
def words(lst):
    if not isinstance(lst, (tuple, list, set, frozenset)):
        raise ValueError("Input must be a collection of strings")
    graphs = list(map(word_graph, lst))
    out = graphs[0]
    for gph in graphs[1: ]:
        out = nx.disjoint_union(out, gph)
    return out

# @export
def grid_graph(mval, nval):
    """
    Generate a grid graph of M x N.
    """

    gph = nx.Graph()

    for xval, yval in product(range(mval), range(nval)):
        if xval + 1 < mval:
            gph.add_edge((xval, yval), (xval + 1, yval))
        if yval + 1 < nval:
            gph.add_edge((xval, yval), (xval, yval + 1))
    return gph

# @export
def problem(mval, nval, wordlist=PLANETS):

    if not (all(isinstance(_, INTS) and _ > 0 for _ in [mval, nval])):
        raise ValueError("Inputs {} ({}), {}({}) must be positive integers".format(
            mval, type(mval), nval, type(nval)))

    return LabeledHomomorphism(words(wordlist), grid_graph(mval, nval))



