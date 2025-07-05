from z3 import *
from itertools import combinations
from math import ceil
import time
import numpy as np
from .encodings import *
import multiprocessing

from z3 import *
from itertools import combinations
from math import ceil
import time
import numpy as np
from .encodings import *
import multiprocessing

def extract_schedule(model, home, away, teams, weeks, periods):
    sched = [[None] * weeks for _ in range(periods)]
    for w in range(weeks):
        for p in range(periods):
            home_team = None
            away_team = None
            for i in teams:
                if is_true(model.evaluate(home[i, w, p], model_completion=True)):
                    home_team = i + 1
                if is_true(model.evaluate(away[i, w, p], model_completion=True)):
                    away_team = i + 1
            sched[p][w] = [home_team, away_team]
    return sched


def _sat_worker(queue, n, timeout, optimize, encoding):
    start_time = time.time()
    weeks = n - 1
    periods = n // 2
    teams = list(range(n))

    home = np.empty((n, weeks, periods), dtype=object)
    away = np.empty((n, weeks, periods), dtype=object)
    for t in teams:
        for w in range(weeks):
            for p in range(periods):
                home[t, w, p] = Bool(f"H_{t}_{w}_{p}")
                away[t, w, p] = Bool(f"A_{t}_{w}_{p}")

    if encoding == 'np':
        exactly_one = exactly_one_np
        at_least_k = at_least_k_np
        at_most_k = at_most_k_np
    else:
        at_least_k = at_least_k_seq
        at_most_k = at_most_k_seq
        if encoding == 'he':
            exactly_one = exactly_one_he
        elif encoding == 'seq':
            exactly_one = exactly_one_seq
        elif encoding == 'bw':
            exactly_one = exactly_one_bw

    def build_solver(imbalance=None):
        s = Solver()
        s.set("random_seed", 42)
        for w in range(weeks):
            for p in range(periods):
                s.add(exactly_one([home[t, w, p] for t in teams], name=f"slot_home_{w}_{p}"))
                s.add(exactly_one([away[t, w, p] for t in teams], name=f"slot_away_{w}_{p}"))
        for t in teams:
            for w in range(weeks):
                vars_in_week = [home[t, w, p] for p in range(periods)] + [away[t, w, p] for p in range(periods)]
                s.add(exactly_one(vars_in_week, name=f"team_plays_{t}_{w}"))
        for i, j in combinations(teams, 2):
            match_slots = []
            for w in range(weeks):
                for p in range(periods):
                    match_slots.append(
                        Or(And(home[i, w, p], away[j, w, p]),
                           And(home[j, w, p], away[i, w, p]))
                    )
            s.add(exactly_one(match_slots, name=f"pair_meets_{i}_{j}"))
        for t in teams:
            for p in range(periods):
                games = [home[t, w, p] for w in range(weeks)] + [away[t, w, p] for w in range(weeks)]
                s.add(at_most_k(games, 2, name=f"team_{t}_period_{p}"))
        
        if optimize and imbalance is None: #we are in the optimization case, and in particular we are in its first iteration (the one that simply checks the decision problem)
            print(f'trying to optimize with no imbalance, just decision problem')

        if optimize and imbalance is not None: #we are in the optimization case, and in particular not in its first iteration (the one that simply checks the decision problem)
            min_home = (weeks // 2) - imbalance
            max_home = (weeks + 1) // 2 + imbalance
            print(f'trying to optimize with min_home={min_home} and max_home={max_home}')
            for t in teams:
                home_games = [home[t, w, p] for w in range(weeks) for p in range(periods)]
                s.add(at_least_k(home_games, min_home, f"home_min_{t}"))
                s.add(at_most_k(home_games, max_home, f"home_max_{t}"))
        return s
    
    def decision_problem_feasible():
        s = build_solver()
        result = s.check()
        if result != sat:
            elapsed = time.time() - start_time
            queue.put((elapsed, False, None, None))
            return False
        m = s.model()
        sched = extract_schedule(m, home, away, teams, weeks, periods)
        elapsed = time.time() - start_time
        queue.put((elapsed, True, None, sched))
        return True


    if optimize:
        # Always check decision problem first
        if not decision_problem_feasible():
            return

        low, high = 0, weeks // 2
        best_model = None
        best_imbalance = None
        best_sched = None

        while low <= high:
            mid = (low + high) // 2
            s = build_solver(mid)
            if s.check() == sat:
                best_model = s.model()
                best_imbalance = mid
                best_sched = extract_schedule(best_model, home, away, teams, weeks, periods)
                queue.put((time.time() - start_time, (best_imbalance == 0), best_imbalance, best_sched))
                high = mid - 1
            else:
                low = mid + 1
            elapsed = time.time() - start_time

        if best_model is None:
            queue.put((elapsed, False, None, None))
            return

        optimal = (best_imbalance == 0 and elapsed < timeout)
        queue.put((elapsed, optimal, best_imbalance, best_sched))

    else:
        decision_problem_feasible()

def sports_scheduling_sat_multiprocess(n, timeout=300, optimize=True, encoding='heule'):

    if encoding not in ['he', 'seq', 'np', 'bw']:
        raise ValueError(f"Unsupported encoding: {encoding}. Supported encodings are 'heule', 'seq', 'np' and 'bw'.")
    else:
        if encoding == 'np':
            exactly_one = exactly_one_np
            at_least_k = at_least_k_np
            at_most_k = at_most_k_np
        else:
            at_least_k = at_least_k_seq
            at_most_k = at_most_k_seq
            if encoding == 'he':
                exactly_one = exactly_one_he
            elif encoding == 'seq':
                exactly_one = exactly_one_seq
            elif encoding == 'bw':
                exactly_one = exactly_one_bw
    """  basically we have all the following combinations of models:
            - heule:   heule encoding for one-cardinality constraints, sequential encoding for k-cardinality constraints
            - seq:     sequential encoding for all constraints
            - np:      naive pairwise encoding for all constraints
            - bw:      binary bitwise encoding for one-cardinality constraints, sequential encoding for k-cardinality constraints"""

    queue = multiprocessing.Queue()
    p = multiprocessing.Process(target=_sat_worker, args=(queue, n, timeout, optimize, encoding))
    p.start()
    p.join(timeout)

    last_result = None
    while not queue.empty():
        last_result = queue.get()
    
    if p.is_alive(): #case where, when the timeout expired, # the process is still running
        p.terminate()
        p.join()
        # If the process was terminated due to timeout, return the last useful result with timeout as elapsed time
        if last_result is not None:
            return timeout, last_result[1], last_result[2], last_result[3]
        else:
            return timeout, False, None, None
    else:
        # If the process finished autonomously, return the last result
        if last_result is not None:
            return last_result
        else:
            return timeout, False, None, None