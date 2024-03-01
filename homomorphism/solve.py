"""
  A useful solve wrapper.
"""
from typing import Tuple, Dict, List, Any, Iterable
from threading import Timer
from itertools import chain
from pysat.formula import CNF
from pysat.solvers import Solver

PROOF = List[str] | None
STATUS = bool | None
MODEL = List[int] | None
MODELS = List[MODEL]
SOLVER = str | Solver
STATS = Dict[str, Any]

def enumerate_models(solveit: Solver,
                     time_limit: int = -1) -> Iterable[MODEL]:
    """
      Produce an iterable of all models.
      status (first returned) will say whether it finished.
    """
    if time_limit > 0:
        def interrupt(solve):
            solve.interrupt()
        my_time = Timer(time_limit, interrupt, [solveit])
        my_time.start()
        try:
            while True:
                status = solveit.solve_limited(expect_interrupt=True)
                stats = solveit.accum_stats().copy()
                stats['time'] = solveit.time()
                if status is None:
                    yield stats, None
                    return
                elif not status:
                    yield stats, []
                    return
                else:
                    model = solveit.get_model()
                    yield stats, model
                    solveit.add_clause([-_ for _ in model])
        except NotImplementedError: # we can't handle it
            my_time.cancel()
            print("Time limit unavailable")

    # Do it the regular way
    while True:
        status = solveit.solve()
        stats = solveit.accum_stats().copy()
        stats['time'] = solveit.time()
        if not status:
            yield stats, []
            return
        model = solveit.get_model()
        yield stats, model
        solveit.add_clause([-_ for _ in model])

def solve_cnf(cnf: CNF,
              solver:SOLVER ='cadical153',
              use_timer: bool = True,
              with_proof: bool = False,
              time_limit: int = -1,
              **kwds) -> Tuple[Iterable[MODEL], PROOF]:
    """ Solve the constructed model """

    if isinstance(solver, str):
        solveit = Solver(
            name=solver,
            bootstrap_with=cnf,
            with_proof=with_proof,
            use_timer=use_timer,
            **kwds)
        # Check that it's one of our solvers
    elif isinstance(solver, Solver):
        solveit = solver(
            bootstrap_with = cnf,
            with_proof = with_proof,
            use_timer = use_timer,
            **kwds)
    else:
        raise ValueError(f"solver {solver} is not a string or Solver")

    proof = None # Only given if original solution is UNSAT
    models = enumerate_models(solveit, time_limit = time_limit)
    first = next(models)
    # This is either List[int] or None
    # in both cases there's no proof
    # This will either be None or a List[int]
    if first[1] == []: # UNSAT
        # It's UNSAT
        if with_proof:
            try:
                proof = solveit.get_proof()
            except NotImplementedError:
                print(f"solver {solver} cannot get unsat proof")
    return chain([first], models), proof
