"""
Given a labeled undirected graph G, and an undirected graph H create a SAT
encoding of the labeled homomorphism problem from G --> H.
"""
from typing import List, Tuple, Dict, Iterable, Hashable, Set
from math import ceil
from itertools import product, combinations, chain, islice
from more_itertools import bucket
from collections import Counter
from pysat.formula import CNF, CNFPlus, IDPool
from pysat.solvers import Solver
from pysat.card import EncType, CardEnc
import networkx as nx
from networkx.algorithms import bipartite as bipartite_x
from .solve import solve_cnf
# from utility import export

CLAUSE = List[int]
FUNCTION = Dict[Tuple[str, Hashable, Hashable], int]
PLACEMENT = Dict[Tuple[int, int], str]

def is_undirected(gph):
    """ Test for undirected graph """
    return isinstance(gph, nx.Graph) and (not gph.is_directed())

def and_def(res, lita, litb):
    """
    res <==> vara AND varb

    ~res OR lita
    ~res OR litb
    res OR ~lita OR ~litb
    """

    return [[-res, lita], [-res, litb], [res, -lita, -litb]]

def parity_def(vpool: IDPool, lita: int, litb: int) -> Tuple[int, List[int]]:
    """
    res <==> vara != varb
    res + vara + varb = 0 -- parity
    Forbid (1,0,0), (0,1,0), (0,0,1), (1,1,1)
    """
    res = vpool.id()
    return (res,
            [[-res, lita, litb],
             [res, -lita, litb],
             [res, lita, -litb],
             [-res, -lita, -litb]])

def compatible(arg1: PLACEMENT, arg2: PLACEMENT) -> bool:
    """ Check compatibility of two assignments of letters to squares """
    common = set(arg1.keys()).intersection(arg2.keys())
    return all((arg1[_] == arg2[_] for _ in common))

def new_function_def(vpool: IDPool, stem: str,
                     domain: Set[Hashable],
                     frange: Set[Hashable],
                     partial: bool = False,
                     pairwise: bool = False) -> Tuple[FUNCTION, Iterable[CLAUSE]]:

    counter = CardEnc.atmost if partial else CardEnc.equals
    fvars = {key : vpool.id((stem, key))
        for key in product(domain, frange)}
    encoding = EncType.pairwise if pairwise else EncType.ladder
    clauses = chain(*(counter(
        lits = [fvars[elt, _] for _ in frange],
        bound = 1,
        vpool = vpool,
        encoding = encoding).clauses for elt in domain))

    return fvars, clauses

def function_def(vpool: IDPool, fvars: Dict[Tuple[Hashable, Hashable], int],
                 partial: bool = False, pairwise: bool = False) -> Iterable[CLAUSE]:
    """ Define a function (possibly partial) """
    counter = CardEnc.atmost if partial else CardEnc.equals
    domain = set((_[0] for _ in fvars.keys()))
    frange = set((_[1] for _ in fvars.keys()))
    encoding = EncType.pairwise if pairwise else EncType.ladder
    for elt in domain:
        yield from counter(lits = [fvars[elt, _] for _ in frange],
                           bound = 1,
                           vpool = vpool,
                           encoding = encoding)

class LabeledHomomorphismModel:
    pass

# @export
class LabeledHomomorphism:
    """
    grphG, grphH are both networkx graphs.
    grphG must have an node attribute 'label'

    If coloring is True, then we use coloring variables instead of the second
    condition below.

    We will have the following variables:

    x[v,w]: where v in G, w in H, true if v maps to w
    Constraints:
    For all v in G ExactlyOne({x[v,w] for w in H}): i.e. f is a function.
    for all (v,v') in E(G): (f(v), f(v')) in E(H)
    This is equivalent to (x[v,w] AND x[v',w']) ==> (w,w') in E(G).
    However, the right hand side is known at problem specification time.
    This is equivalent to
    For All (w,w') not in E(G): ~x[v,w] OR ~x[v',w'].

    That takes care of homomorphism.  Now we take care of the labels.

    The condition is that if f(v) = f(v') then l(v) = l(v').
    The former conditions is the same as
    x[v,w] = x[v',w] for all w
    In contrapositive:
    For all v,v' such that l(v) != l(v') there exists w such that x[v,w] == T and = x[v',w] == F.
    We define y[v,v',w] = x[v,w] AND ~x[v',w]


    The condition then is: For all v,v' such that l(v) != l(v'): OR_w y[v,v',w].

    Alternate encoding:

    Create variables z[w,c], for all w in H and c in the labels indicating
    that w is assinged label c.

    Constraints:

    AtMost1([z[w,c] for c in labels]) for all w in H

    x[v,w] ==> z[w,l(v)] for all v in G, w in H.

    Cardinality conditions will help:

    sum_w z[w,c] <= #{v in G: l(v) = c}

    Special extra conditions if both G and H are bipartite.

    Here's another way of doing this:

    Form a new graph G' which is the union of two disjoint copies of G
    where we also add an edge between a node in G and a node n G' if they have different labels.
    """

    def __init__(self, gph_G, gph_H):
        if not (is_undirected(gph_G) and is_undirected(gph_H)):
            raise ValueError("Inputs must be undirected graphs")

        # test if G has an attribute called label
        if not (all(('label' in gph_G.nodes[_] for _ in gph_G.nodes))):
            raise ValueError("G must have the attribute label for each node")

        self._gph_G = gph_G.copy()
        self._gph_H = gph_H.copy()
        self._labels = dict( (_, gph_G.nodes[_]['label']) for _ in gph_G.nodes )

    def model(self,
              color: bool = True,
              non_color: bool = True,
              bipartite: bool = True,
              lbound: bool = True,
              hbound: bool = True,
              verbose: int = 0,
              pairwise: bool = False,
              direct: bool = False,
              cardinality = EncType.seqcounter):
        """ Construct the SAT model """
        return LabeledHomomorphismModel(self,
                                        bipartite = bipartite,
                                        color = color,
                                        non_color = non_color,
                                        lbound = lbound,
                                        hbound = hbound,
                                        verbose = verbose,
                                        pairwise = pairwise,
                                        direct = direct,
                                        cardinality = cardinality)

# @export
class LabeledHomomorphismModel:
    """
      Solve the labeled homomorphism problem:

      There are the following variables:
      x[v,w] for v in V(G) and w in V(H) indicating that f(v) = w
      This is a function if and only if
      sum([x[v,w] for w in V(G)]) = 1 for all v.  That is every v in V(G)
      is mapped to exactly one w in V(H).
      z[w,c] for w in V(H) and c in C indicating that l(w) = c.  Again
      sum([z[w,c] for c in C]]) <= 1 for all w. That is every w in V(H)
      is mappend to at most one c in C (it is a partial function).
      But we must have (OR [x[v,w] for v in w]) ==> sum(..) = 1.
      That is, if w = f(v) for some v, then w gets a color.

      We have (l(v) = c AND x[v,w]) ==> z[w,c]
      i.e. (l(v) != c) OR ~x[v,w] OR z[w,c] for all v
      or ~x[v,w] OR z[w,c] for all v such that l(v) = c and for all w
      or ~x[v,w] OR z[w,l(v)] for all v in V(G), w in V(H)
      """

    def __init__(self, parent,
                 bipartite: bool = True,
                 color: bool = True,
                 non_color: bool = False,
                 lbound: bool = True,
                 hbound: bool = True,
                 verbose: int = 0,
                 pairwise: bool = False,
                 direct: bool = False,
                 cardinality: int = EncType.seqcounter):

        if not isinstance(parent, LabeledHomomorphism):
            raise ValueError("Parent must be of class LabeledHomomorphism")

        self._parent = parent
        self._gph_G = parent._gph_G
        self._gph_H = parent._gph_H
        self._labels = parent._labels
        self._verbose = verbose
        self._solveit = None
        self._proof = None
        self._mappings = None
        self._pairwise = pairwise
        self._cardinality = cardinality
        self._stats = None
        self._placements = None
        self._errors = None
 
        self._pool = IDPool() # the variable pool
        self._cnf = CNF()
        self._xvars, xclauses = new_function_def(self._pool, 'x',
            set(self._gph_G.nodes),
            set(self._gph_H.nodes),
            pairwise = self._pairwise)
        self._cnf.extend(xclauses)

        self._red_edges = [edge for edge in combinations(self._gph_G.nodes,2)
            if not self._gph_G.has_edge(*edge)
            and self._labels[edge[0]] != self._labels[edge[1]]]
            
                
        # self._xvars = dict(
        #     ((vnode, wnode), self._pool.id(('x', (vnode, wnode))))
        #     for vnode, wnode in product(self._gph_G.nodes, self._gph_H.nodes)
        # )
        # self._cnf.extend(function_def(self._pool, self._xvars, pairwise = self._pairwise))
        if direct:
            self.homomorphism_clauses_direct()
        else:
            self.homomorphism_clauses()

        if bipartite:
            self.bipartite_clauses()

        if not (color or non_color):
            raise ValueError("Must specify at least one of color/non color")
        if color:
            self.color_clauses()
            if lbound or hbound:
                self.bound_clauses(lbound, hbound)
        if non_color:
            self.non_color_clauses()

    def bipartite_clauses(self):
        """
        If G and H are both bipartite, we can add extra conditions
        """
        if not (nx.is_bipartite(self._gph_G) and nx.is_bipartite(self._gph_H)):
            return # Nothing extra can be don

        # Find connected components of G and H, an then take the bipartite split of each
        subgraphg = [nx.subgraph(self._gph_G, _)
                     for _ in nx.connected_components(self._gph_G)]
        splitsg = list(map(bipartite_x.sets, subgraphg))
        ncompg = len(splitsg)
        subgraphh = [nx.subgraph(self._gph_H, _)
                     for _ in nx.connected_components(self._gph_H)]
        splitsh = list(map(bipartite_x.sets, subgraphh))
        ncomph = len(splitsh)
        # We have one boolean variable for each component
        self._bvars = dict( (_, self._pool.id(('c', _))) for _ in range(ncompg * ncompg) )
        # bvar[c] ==> elements of gbot in c maps to hbot
        # and element of gtop in c maps to htop
        # and similarly for ~bvar[c]

        for ind, ((gtop, gbot), (hbot, htop)) in enumerate(product(splitsg, splitsh)):
            # bvars[ind] means that elements of gbot map to hbot
            # and gtop map to htop
            # ~bvars[ind] means that elements of gbot map to htop
            # and gtop map to hbot
            bvar = self._bvars[ind]
            for vnode in gbot:
                self._cnf.extend([ [-bvar, -self._xvars[vnode, wnode]]
                                   for wnode in htop])
                self._cnf.extend([ [bvar, -self._xvars[vnode, wnode]]
                                   for wnode in hbot])

            for vnode in gtop:
                self._cnf.extend([ [-bvar, -self._xvars[vnode, wnode]]
                                   for wnode in hbot])
                self._cnf.extend([ [bvar, -self._xvars[vnode, wnode]]
                                   for wnode in htop])

    def homomorphism_clauses(self):
        # Map edges to edges
        # If (v,vp) is an edge of G then (f(v), f(vp)) is an edge of H
        # Equivalently (v,vp) in E(G): x[v,w] AND x[vp,wp] ==> (w,wp) in E(H)
        # Contrapositive: (w,wp) not in E(H) ==> ~x[v,w] OR ~x[vp,wp]
        # if (v,v') is an edge of G, and (w,w') is not an edge of H
        # then it is not true that f(v) = w and f(v') = w'
        for vnode, vnodep in self._gph_G.edges:
            for wnode, wnodep in product(self._gph_H.nodes, repeat=2):
                if not self._gph_H.has_edge(wnode, wnodep):
                    self._cnf.append(
                        [-self._xvars[vnode, wnode], -self._xvars[vnodep, wnodep]])

    def homomorphism_clauses_direct(self):
        # Map edges to edges
        # Let v be in V(G), and v maps to w in V(H). If vp is a neighbor of v,
        # then vp must map to a neighbor of w

        for vnode in self._gph_G.nodes:
            for wnode in self._gph_H.nodes: # vnode --> wnode
                antecedent = [-self._xvars[vnode, wnode]]
                for vnodep in self._gph_G.neighbors(vnode):
                    # if vnode --> wnode then a neighbor of vnode must be mapped
                    # to a neighbor of wnode
                    self._cnf.extend([antecedent + clause
                                      for clause in CardEnc.equals(
                                          lits = [self._xvars[vnodep, _]
                                              for _ in self._gph_H.neighbors(wnode)],
                                          vpool = self._pool,
                                          bound = 1,
                                          encoding = EncType.ladder)])

    def color_clauses(self):
        """ Add clauses from coloring the nodes of both graphs """

        self._max_occurence = Counter(self._labels.values())
        self._zvars, zclauses = new_function_def(self._pool, 'z',
            set(self._gph_H.nodes),
            set(self._labels.values()),
            partial = True,
            pairwise = self._pairwise)
        self._cnf.extend(zclauses)
        # self._zvars = dict(
        #     ((wnode, cnode), self._pool.id(('z', (wnode, cnode))))
        #     for wnode, cnode in product(self._gph_H.nodes, self._max_occurence.keys())
        # )
        # self._cnf.extend(function_def(self._pool, self._zvars,
        #                               pairwise = self._pairwise,
        #                               partial=True,))
        # Find label pairs that must occur
        # If v is colored by c, then f(v) is colored by c

        self._cnf.extend([[-xvar, # f(v) = w
                           self._zvars[wnode, self._labels[vnode]]] # l(w) = l(v)
                          for (vnode, wnode), xvar in self._xvars.items()])

    def bound_clauses(self, lbound: bool, hbound: bool):
        
        labeled_edges = set(
            (frozenset((self._labels[_[0]], self._labels[_[1]]))
                       for _ in self._gph_G.edges))
        # if a letter occurs in Q pairs
        # then it has to occur at least ceil(A/ max_deg(H)) times
        edge_counts = {letter: len([_ for _ in labeled_edges if letter in _])
            for letter in self._max_occurence.keys()}
        if self._verbose > 0:
            print(f"edge_counts = {edge_counts}")
        # find the max degree of H
        max_deg_H = max((deg for _, deg in self._gph_H.degree()))
        # min occurence
        if lbound:
            self._min_occurence = {letter: ceil(deg / max_deg_H)
                for letter, deg in edge_counts.items()}
            if self._verbose > 0:
                print(f"min_occurence = {self._min_occurence}")
            # The number of nodes in H colored by c is <= the number of such nodes in G
            for color in self._min_occurence.keys():
                zlits = [self._zvars[_, color] for _ in self._gph_H.nodes]
                self._cnf.extend(
                    CardEnc.atleast(lits=zlits,
                                    vpool=self._pool,
                                    bound = self._min_occurence[color],
                                    encoding = self._cardinality))
            
        if hbound:
            for color in self._max_occurence.keys():
                zlits = [self._zvars[_, color] for _ in self._gph_H.nodes]
                self._cnf.extend(
                    CardEnc.atmost(lits=zlits,
                                    vpool=self._pool,
                                    bound = self._max_occurence[color],
                                    encoding = self._cardinality))

    def non_color_clauses(self):
        """ Generic clauses for labeled homomorphism """
        # For all W, there exists (v,v') such that y[v,v',w]
        # for all v != vp, f(v) = f(vp) ==> l(v) = l(vp)
        # Contrapositive:
        # for all v != vp, l(v) != l(vp) ==> f(v) != f(vp)
        # f(v) != f(vp) <==> exists w such that f(v) = w and f(vp) != w
        # Two nodes with different labels cannot map to the same
        # node.  We can exclude pairs that are connected by an edge
        # since the homomorphism condition will exclude those too.
        for vnode, vnodep in self._red_edges:
            self._cnf.extend([[- self._xvars[vnode, _],
                               - self._xvars[vnodep, _]]
                              for _ in self._gph_H.nodes])
                # wclause = []
                # for wnode in self._gph_H.nodes:
                #     yvar, clauses = parity_def(
                #         self._pool,
                #         self._xvars[vnode, wnode],
                #         self._xvars[vnodep, wnode])
                #     self._cnf.extend(clauses)
                #     wclause.append(yvar)
                # self._cnf.append(wclause)

    def edge_clauses(self):
        self._edge_function, clauses = new_function_def(self._pool,
            map(frozenset, chain(self._gph_G.edges, self._red_edges)),
            map(frozenset, combinations(self._gph_H.nodes, 2)),
            pairwise = self._pairwise)

        self._cnf.extend(clauses)
        # Map like colors to like colors
        self._cnf.extend([-self._edge_function[frozenset(g_edge), frozenset(h_edge)]]
                         for g_edge in self._gph_G.edges
                         for h_edge in combinations(self._gph_H.vertices, 2)
                         if not self._gph_H.has_edge(h_edge))
        
        self._cnf.extend([-self._edge_function[frozenset(g_edge), frozenset(h_edge)]]
                         for g_edge in self._red_edges
                         for h_edge in self._gph_H.edges)
        # Now for the M^G X = Y M^H
        for wnode in self._gph_H.nodes:
            for edge in chain(self._gph_G.edges, self._red_edges):
                lhs = [- self._xvars[edge[0], wnode], - self._xvars[edge[1], wnode]]
                rhs = [self._edge_function[frozenset([_, wnode]), frozenset(edge)]
                    for _ in self._gph_H.nodes if _ != wnode]
                self._cnf.extend(CardEnc.equals(lits = lhs + rhs,
                                                bound = 2,
                                                vpool = self._pool,
                                                encoding = self._cardinality))

    def solve(self, solver='cadical153',
              use_timer = True,
              with_proof = False,
              time_limit = -1,
              num_soln: int = 1,
              **kwds):
        """ Solve the constructed model """

        if not hasattr(self, '_cnf'):
            raise ValueError("Must call model first")

        models, self._proof = solve_cnf(self._cnf,
            solver = solver,
            use_timer = use_timer,
            with_proof = with_proof,
            time_limit = time_limit,
            **kwds)
        self._mappings = []
        self._stats = []
        for stats, model in islice(models, num_soln):
            self._stats.append(stats)
            if model is None or model == []: # We timed out is UNSAT
                return
            sat_model = [self._pool.obj(_) for _ in model if _ > 0]
            self._mappings.append(dict([_[1] for _ in sat_model
                                        if _ is not None and _[0] == 'x']))

    def check(self):
        """ Check the results of solving against specification """

        if self._mappings is None:
            raise ValueError("You must run solve first to obtain a mapping")

        self._errors = []
        self._placements = []

        for mapping in self._mappings:
            # first check to make sure that the coloring is compatible
            buckets = bucket(((coord, self._labels[coord[0]])
                for coord in mapping.items()), key=lambda _: _[0])
            target = {coord[1] : set([_[1] for _ in buckets[coord]])
                for coord in buckets}
            conflicts = sum(((_ * (_ - 1)) // 2 for _ in map(len, target.values())))
            # take the first (and, one hopes, the only value)
            target = {key: list(val)[0] for key, val in target.items()}

            # Now check the homomorphism property
            conflicts += sum((not self._gph_H.has_edge(
                mapping[vnode], mapping[vnodep])
                for vnode, vnodep in self._gph_G.edges))
            self._placements.append(target)
            self._errors.append(conflicts)

    def to_cnf(self, name):
        """
        Write a DIMACS CNF file for the model.
        """
        with open(f"{name}.cnf", 'w', encoding='utf8') as fil:
            self._cnf.to_file(fil)

    def to_lp(self, name):
        """
        Write an lp file for the model
        """
        with open(f"{name}.lp",'w', encoding='utf8') as fil:
            self._cnf.to_alien(fil, format='lp')

    @property
    def solve_time(self):
        """ Total solution time """
        if self._stats is None:
            raise ValueError("Model has not been solved!")
        # Total up the time
        return sum((_['time'] for _ in self._stats))
