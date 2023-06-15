"""
Given a labeled undirected graph G, and an undirected graph H create a SAT
encoding of the labeled homomorphism problem from G --> H.
"""

from pysat.formula import CNF, CNFPlus, IDPool
from pysat.solvers import Glucose4, Lingeling, Cadical, Solver
from pysat.card import EncType, CardEnc
import networkx as nx
from networkx.algorithms import bipartite
from itertools import product, combinations
from collections import Counter
from threading import Timer
# from utility import export

def is_undirected(gph):
    return isinstance(gph, nx.Graph) and (not gph.is_directed())

def and_def(res, lita, litb):
    """
    res <==> vara AND varb

    ~res OR lita
    ~res OR litb
    res OR ~lita OR ~litb
    """

    return [[-res, lita], [-res, litb], [res, -lita, -litb]]

def parity_def(lita, litb, vpool):
    """
    res <==> vara != varb
    res + vara + varb = 0 -- parity
    Forbid (1,0,0), (0,1,0), (0,0,1), (1,1,1)
    """
    vpool.top += 1
    res = vpool.top
    return res, [[-res, lita, litb], [res, -lita, litb], [res, lita, -litb], [-res, -lita, -litb]]

class LabeledHomomorphismModel(object):
    pass

# @export
class LabeledHomomorphism(object):
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

    def __init__(self, gphG, gphH):
        if not (is_undirected(gphG) and is_undirected(gphH)):
            raise ValueError("Inputs must be undirected graphs")

        # test if G has an attribute called label
        if not (all(('label' in gphG.nodes[_] for _ in gphG.nodes))):
            raise ValueError("G must have the attribute label for each node")

        self._gphG = gphG.copy()
        self._gphH = gphH.copy()
        self._labels = dict( (_, gphG.nodes[_]['label']) for _ in gphG.nodes )

    def model(self, coloring=True, bip=True, cardinality=EncType.seqcounter):
        return LabeledHomomorphismModel(self, bip=bip, coloring=coloring, cardinality=cardinality)

# @export
class LabeledHomomorphismModel(object):

    def __init__(self, parent, bip=True, coloring=True, cardinality=EncType.seqcounter):

        if not isinstance(parent, LabeledHomomorphism):
            raise ValueError("Parent must be of class LabeledHomomorphism")

        self._parent = parent
        self._gphG = parent._gphG
        self._gphH = parent._gphH
        self._labels = parent._labels
        
        self._pool = IDPool() # the variable pool
        self._cnf = CNFPlus() # I don't know if this works
        self._xvars = dict(
            ((vnode, wnode), self._pool.id(('x', (vnode, wnode))))
            for vnode, wnode in product(self._gphG.nodes, self._gphH.nodes)
        )
        # f is a function
        for vnode in self._gphG.nodes:
            self._cnf.extend(CardEnc.equals(lits=[self._xvars[vnode, _] for _ in self._gphH.nodes],
                                            vpool=self._pool,
                                            encoding=EncType.ladder, bound=1))
        
        # Map edges to edges
        # If (v,v') is an edge of G then (f(v), f(v')) is an edge of H
        # <==> (v,v') in E(G): x[v,w] AND x[v,w'] ==> (w,w') in E(H)
        # if (v,v') is an edge of G, and (w,w') is not an edge of H
        # then it is not true that f(v) = w and f(v') = w'
        for vnode, vnodep in self._gphG.edges:
            for wnode, wnodep in product(self._gphH.nodes, repeat=2):
                if not self._gphH.has_edge(wnode, wnodep):
                    self._cnf.append([-self._xvars[vnode, wnode], -self._xvars[vnodep, wnodep]])

        if bip:
            self.bipartite_clauses()
        self._bipartite = bip

        if coloring:
            self.color_clauses(cardinality=cardinality)
            self._cardinality = cardinality
        else:
            self.non_color_clauses()
        self._coloring = coloring

    def bipartite_clauses(self):
        """
        If G and H are both bipartite, we can add extra conditions
        """
        if not (nx.is_bipartite(self._gphG) and nx.is_bipartite(self._gphH)):
            return # Nothing extra can be don

        # Find connected components of G and H, an then take the bipartite split of each
        subgraphg = [nx.subgraph(self._gphG, _) for _ in nx.connected_components(self._gphG)]
        splitsg = list(map(bipartite.sets, subgraphg))
        ncompg = len(splitsg)
        subgraphh = [nx.subgraph(self._gphH, _) for _ in nx.connected_components(self._gphH)]
        splitsh = list(map(bipartite.sets, subgraphh))
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
        
    def color_clauses(self, cardinality=EncType.seqcounter):
        color_counts = Counter([self._labels[_] for _ in self._gphG.nodes])
        self._zvars = dict(
            ((wnode, cnode), self._pool.id(('z', (wnode, cnode))))
            for wnode, cnode in product(self._gphH.nodes, color_counts.keys())
        )
        # every node in H gets at most 1 color
        for wnode in self._gphH.nodes:
            # I think that ladder is best for atmost 1
            self._cnf.extend(CardEnc.atmost(lits=[self._zvars[wnode, _] for _ in color_counts.keys()],
                                            vpool=self._pool, bound=1, encoding=EncType.ladder))

        # If v is colored by c, then f(v) is colored by c
        self._cnf.extend([[-self._xvars[vnode, wnode], self._zvars[wnode, self._labels[vnode]]]
                          for vnode, wnode in product(self._gphG.nodes, self._gphH.nodes)])

        # The number of nodes in H colored by c is <= the number of such nodes in G
        for color, count in color_counts.items():
            zlits = [self._zvars[_, color] for _ in self._gphH.nodes]
            # Every color must appear at least once
            self._cnf.append(zlits)
            if cardinality != -1:
                self._cnf.extend(CardEnc.atmost(lits=zlits, vpool=self._pool, bound=count, encoding=cardinality))

    def non_color_clauses(self):
        # For all W, there exists (v,v') such that y[v,v',w]
        # if l(v) != l(v') then f(v) != f(v')
        # f(v) != f(v') <==> exists w such that f(v) = w and f(v') != w
        for vnode, vnodep in combinations(self._gphG.nodes, 2):
            if self._labels[vnode] != self._labels[vnodep]:
                wclause = []
                for wnode in self._gphH.nodes:
                    yvar, clauses = parity_def(self._xvars[vnode, wnode], self._xvars[vnodep, wnode], self._pool)
                    self._cnf.extend(clauses)
                    wclause.append(yvar)
                self._cnf.append(wclause)
            
    def solve(self, solver='cadical', use_timer=True, with_proof=True, time_limit=-1, **kwds):

        if not hasattr(self, '_cnf'):
            raise ValueError("Must call model first")

        if isinstance(solver, str):
            self._solveit = Solver(name=solver, bootstrap_with=self._cnf,
                                   with_proof=with_proof,
                                   use_timer=use_timer,
                                   **kwds)
            # Check that it's one of our solvers
        else:
            self._solveit = solver(bootstrap_with=self._cnf,
                                   with_proof=with_proof,
                                   use_timer=use_timer,
                                   **kwds)
        if time_limit > 0:
            def interrupt(solve):
                solve.interrupt()
            my_time = Timer(time_limit, interrupt, [self._solveit])
            my_time.start()
            try:
                self._status = self._solveit.solve_limited(expect_interrupt=True)
                self._solveit.clear_interrupt()
            except NotImplementedError as msg:
                my_time.cancel()
                self._status = self._solveit.solve()
        else:
            self._status = self._solveit.solve()

        if self._status:
            # extract the mapping
            sat_model = [self._pool.obj(_) for _ in self._solveit.get_model() if _ > 0]
            self._mapping = dict([_[1] for _ in sat_model if _ is not None and _[0] == 'x'])

        elif self._status == False:
            # self._core = self._solveit.get_core()
            try:
                self._proof = self._solveit.get_proof()
            except NotImplementedError:
                print("solver cannot get unsat proof")
            
    def check(self):

        if not hasattr(self, '_mapping'):
            raise ValueError("You must run solve first to obtain a mapping")

        target = dict()
        # first check to make sure that the coloring is compatible

        conflicts = 0
        for vnode, wnode in self._mapping.items():
            lab = self._labels[vnode]
            if wnode in target and target[wnode] != lab:
                conflicts += 1
            else:
                target[wnode] = lab

        # Now check the homomorphism property
        
        
        for vnode, vnodep in self._gphG.edges:
            target_edge = (self._mapping[vnode], self._mapping[vnodep])
            if not self._gphH.has_edge(*target_edge):
                conflicts += 1

        return target, conflicts

    def to_cnf(self, name):
        """
        Write a DIMACS CNF file for the model.
        """
        with open("{}.cnf".format(name), 'w') as fil:
            self._cnf.to_file(fil)

    def to_lp(self, name):
        """
        Write an lp file for the model
        """
        with open("{}.lp".format(name),'w') as fil:
            self._cnf.to_alien(fil, format='lp')

    @property
    def solve_time(self):
        if hasattr(self, '_solveit'):
            return self._solveit.time()
        else:
            raise ValueError("Model has not been solved!")
        
