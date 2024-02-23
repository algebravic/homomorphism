"""Use z3 to solve the labeled homomorphism problem

Implement a graph as a pair: A set of nodes (which is a set of integers) and a set of ordered pairs of integers.
Let V be the first set, and E the second.
For all (v1,v2) in E: (v1 in V) AND (v2 in V)

If G is undirected then
For all (v1, v2) in E: (v2, v1) in E

We are given two graphs G1, G2, and a function l: G1 --> some finite set [the labels]

We want a function f:G1.V ---> G2.V such that

For all (v1, v2) in G1.E: (f(v1), f(v2)) in G2.E
For all v1 in G1.V, v2 in G1.V: (l(v1) != l(v2) ==> f(v1) != f(v2))

Note: we need the following function:

from networkx.relabel import convert_node_labels_to_integers

convert_node_labels_to_integers(G, first_label=0, ordering='default', label_attribute=None)

Returns a copy of the graph G with the nodes relabeled using consecutive integers.

Parameters
G (graph) – A NetworkX graph

first_label (int, optional (default=0)) – An integer specifying the
starting offset in numbering nodes. The new integer labels are
numbered first_label, …, n-1+first_label.

ordering (string) – “default” : inherit node ordering from G.nodes()
“sorted” : inherit node ordering from sorted(G.nodes()) “increasing
degree” : nodes are sorted by increasing degree “decreasing degree” :
nodes are sorted by decreasing degree

label_attribute (string, optional (default=None)) – Name of node
attribute to store old label. If None no attribute is created.

"""

from itertools import combinations
from networkx.relabel import convert_node_labels_to_integers
from z3 import (ForAll, Implies, IntSort, TupleSort, EmptySet, IsMember, SetAdd,
                Function, Array, ArraySort, Store, String, Solver, Const, And, StringSort, Var)

pair, mk_pair, (first, second) = TupleSort('pair', [IntSort(), IntSort()])

def relabel_graph(gph, label_attr='old_label'):

    ngph = convert_node_labels_to_integers(gph,label_attribute=label_attr)
    # Now get the translation dict
    dct = dict(((ngph.nodes[_][label_attr], _) for _ in ngph.nodes))
    return ngph, dct

class GraphZ3:
    """
    Take a graph and create Z3 elements for it,

    A graph will have Vertices and Edges.
    Vertices will be a set of integers.
    Edges will be a set of pairs of integers.

    ForAll e in in Edges: first(e) in Vertices AND second(e) in Vertices
    """

    def __init__(self, gph):

        self._gph, self._dict = relabel_graph(gph)
        # building up the sets

        self._edges = EmptySet(pair)
        for (nodea, nodeb) in self._gph.edges:
            self._edges = SetAdd(self._edges, mk_pair(nodea, nodeb))
            self._edges = SetAdd(self._edges, mk_pair(nodeb, nodea))

        self._vertices = EmptySet(IntSort())
        for node in self._gph.nodes:
            self._vertices = SetAdd(self._vertices, node)

        # If s is a set and a is an element, IsMember(a, s) is true if a in s
        # ForAll (e in E): (first(e) in V) AND (second(e) in V)

        evar = Const(f'e_{self._gph.name}', pair)
        self._cond = ForAll(evar, Implies(IsMember(evar, self._edges), And(
            IsMember(first(evar), self._vertices),
            IsMember(second(evar), self._vertices)
        )))

        # if we have labels define that too
        if all(('label' in self._gph.nodes[_] for _ in self._gph.nodes)):
            self._labels = Array('l', IntSort(), StringSort())
            for node in self._gph.nodes:
                self._labels = Store(self._labels, node, String(self._gph.nodes[node]['label']))
        else:
            self._labels = None
        
    @property
    def vertices(self):
        return self._vertices

    @property
    def edges(self):
        return self._edges

    @property
    def labels(self):
        return self._labels

    @property
    def condition(self):
        return self._cond

    
def labeled_homomorphism(gpha, gphb, expand=False, colored=False):
    """
    gpha, gphb are both networkx graphs

    gpha has labeled nodes.  We want a graph homomorphism from gpha to gphb
    such that nodes with different labels are mapped to different nodes.

    We have a basic encoding, and another one using an explicit coloring

    For the colored option: we want another map from nodes of gphb to labels.
    We want g(f(v)) = l(v) for all v.  That is we want a commutative diagram.
    """

    zgpha = GraphZ3(gpha)
    zgphb = GraphZ3(gphb)

    # gpha must have a label
    if zgpha.labels is None:
        raise ValueError("gpha must have a label attribute")
    evar = Const(f'e_{zgpha._gph.name}', pair)
    vvar = Const(f'v_{zgpha._gph.name}', IntSort())
    fun = Function(f'f_{zgpha._gph.name}_{zgphb._gph.name}', IntSort(), IntSort())

    if expand:
        hom_cond = ([IsMember(fun(node), zgphb.vertices) for node in zgpha._gph.nodes]
            + [IsMember(mk_pair(fun(nodea), fun(nodeb)), zgphb.edges)
               for nodea, nodeb in zgpha._gph.edges])
    else:
        hom_cond = [ForAll([evar], Implies(IsMember(evar, zgpha.edges),
                                         IsMember(
                                             mk_pair(fun(first(evar)),
                                                     fun(second(evar))),
                                             zgphb.edges)))]

    if colored:
        gfun = Function(f'g_zgphb._gph.name', IntSort(), StringSort())
        if expand:
            label_cond = [gfun(fun(vnode)) == String(zgpha._gph.nodes[vnode]['label'])
                for vnode in zgpha._gph.nodes]
        else:
            label_cond = [ForAll([vvar], gfun(fun(vvar)) == zgpha.labels[vvar])]
    else:
        if expand:
            label_cond = [fun(vnode) != fun(vnodep)
                for vnode, vnodep in combinations(zgpha._gph.nodes, 2)
                if zgpha._gph.nodes[vnode]['label'] != 
                zgpha._gph.nodes[vnodep]['label']]
        else:
            vvarp = Const(f'vp_{zgpha._gph.name}', IntSort())
            label_cond = [ForAll([vvar, vvarp], Implies(
                And(IsMember(vvar, zgpha.vertices),
                    IsMember(vvarp, zgpha.vertices),
                    zgpha.labels[vvar] != zgpha.labels[vvarp]),
                fun(vvar) != fun(vvarp)
            ))]

            
    return [zgpha.condition, zgphb.condition] + hom_cond + label_cond
