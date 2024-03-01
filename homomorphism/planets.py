from typing import List
from collections import Counter
from itertools import product, combinations
import networkx as nx
import numpy as np
from pysat.card import EncType
from .sat_homomorphism import LabeledHomomorphism
# from .utility import export

LISTS = {'planets': ['mercury', 'venus', 'earth', 'mars', 'jupiter',
                     'saturn', 'uranus', 'neptune', 'pluto'],
         'months': ['january', 'february', 'march', 'april',
                    'may', 'june', 'july', 'august', 'september',
                    'october', 'november', 'december'],
         'dwarfs' : ['bashful', 'grumpy', 'sleepy', 'sneezy',
                     'dopey', 'happy', 'doc'],
         'greek': ['ALPHA', 'BETA', 'GAMMA', 'DELTA',
                   'EPSILON', 'ZETA', 'ETA', 'THETA',
                   'IOTA', 'KAPPA', 'LAMBDA', 'MU', 'NU',
                   'OMICRON', 'XI', 'PI', 'RHO', 'SIGMA',
                   'TAU', 'UPSILON', 'PHI', 'CHI', 'PSI', 'OMEGA']
         }

INTS = (int, np.int8, np.int16, np.int32, np.int64)

def word_graph(word: str) -> nx.Graph:
    """
    word: a string
    """
    if not isinstance(word, str):
        raise ValueError(f"input {word} must be a string")

    gph = nx.Graph()
    for ind, val in enumerate(word):
        gph.add_node(ind, label=val)
    for ind in range(len(word) - 1):
        gph.add_edge(ind, ind + 1)
    return gph

def big_union(lst : List[nx.Graph]) -> nx.Graph:
    """
    Disjoint union of a list of graphs
    """
    if len(lst) > 1:
        half = len(lst) // 2
        left = big_union(lst[: half])
        right = big_union(lst[half: ])
        return nx.disjoint_union(left, right)
    elif len(lst) == 1:
        return lst[0]
    else:
        raise ValueError("Input is empty!")

# @export
def words(ident: str) -> nx.Graph:
    """ The Graph induced by the word list """
    if ident not in LISTS:
        raise ValueError(f"Input not in {tuple(LISTS.keys())}")
    else:
        lst = LISTS[ident]
    if not isinstance(lst, (tuple, list, set, frozenset)):
        raise ValueError("Input must be a collection of strings")
    res = big_union(list(map(word_graph, lst)))
    res.name = ident
    return res

# @export
def grid_graph(mval, nval) -> nx.Graph:
    """
    Generate a grid graph of M x N.
    """

    gph = nx.Graph(name=f'grid_{mval}_{nval}')

    for xval, yval in product(range(mval), range(nval)):
        if xval + 1 < mval:
            gph.add_edge((xval, yval), (xval + 1, yval))
        if yval + 1 < nval:
            gph.add_edge((xval, yval), (xval, yval + 1))
    return gph

# @export
def problem(mval, nval, wordlist='planets'):
    """ Produce the class instance for the problem """
    if not all(isinstance(_, INTS) and _ > 0 for _ in [mval, nval]):
        raise ValueError(f"Inputs {mval} ({type(mval)}), {nval}({type(nval)})"
                         + " must be positive integers")

    return LabeledHomomorphism(words(wordlist), grid_graph(mval, nval))
