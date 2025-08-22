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

    def build_solver(max_home=None):
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

        if optimize and max_home is not None:
            for t in teams:
                home_games = [home[t, w, p] for w in range(weeks) for p in range(periods)]
                s.add(at_most_k(home_games, max_home, name=f"max_home_{t}"))
                s.add(at_least_k(home_games, weeks-max_home, name=f"min_home_{t}"))

        return s

    def decision_problem_feasible():
        s = build_solver()
        result = s.check()
        elapsed = time.time() - start_time
        if result != sat:
            queue.put((elapsed, False, None, None))
            return False

        m = s.model()
        sched = extract_schedule(m, home, away, teams, weeks, periods)
        home_counts = []
        for t in teams:
            home_games = sum(
                1 for w in range(weeks) for p in range(periods)
                if is_true(m.evaluate(home[t, w, p], model_completion=True))
            )
            home_counts.append(home_games)

        max_home = max(home_counts)
        optimal = (max_home == ceil(weeks/2) and elapsed < timeout) or (not optimize)

        if not optimize:
            queue.put((elapsed, optimal, None, sched))
            return True
        else:
            queue.put((elapsed, optimal, max_home, sched))
        return True
    
    if n <= 4 and optimize:
        decision_problem_feasible()
        return

    elif optimize:
        # Binary search to minimize the maximum home games
        # For n=6: weeks=5, ideal max_home = ceil(5/2) = 3
        min_obj = periods  # Lower bound: ideal maximum home games
        max_obj = weeks      # Upper bound: maximum possible home games

        best_model = None
        best_obj = None
        best_sched = None

        while min_obj <= max_obj:
            mid = (min_obj + max_obj) // 2

            print(f"\nTrying maximum home games: {mid}")

            s = build_solver(mid)
            res = s.check()

            if res == sat:
                best_model = s.model()
                best_sched = extract_schedule(best_model, home, away, teams, weeks, periods)
                home_counts = []
                for t in teams:
                    home_games = sum(
                        1 for w in range(weeks) for p in range(periods)
                            if is_true(best_model.evaluate(home[t, w, p], model_completion=True))
                    )
                    home_counts.append(home_games)
                best_obj = max(home_counts)
                
                # Found a solution with max_home = mid, try to find a better one
                max_obj = mid - 1
                print(f"Found solution with max_home = {best_obj}")
            else:
                # No solution with max_home = mid, try a higher value
                min_obj = mid + 1
                print(f"No solution with max_home = {mid}")

        elapsed = time.time() - start_time
        if best_model is None:
            queue.put((elapsed, False, None, None))
            return

        # Check if we found the optimal solution (max_home = ideal_max)
        optimal = (best_obj == min_obj and elapsed < timeout)
        queue.put((elapsed, optimal, best_obj, best_sched))

    else:
        decision_problem_feasible()


def sports_scheduling_sat(n, timeout=300, optimize=True, encoding='he'):
    if encoding not in ['he', 'seq', 'np', 'bw']:
        raise ValueError(f"Unsupported encoding: {encoding}. Supported encodings are 'he', 'seq', 'np' and 'bw'.")

    queue = multiprocessing.Queue()
    p = multiprocessing.Process(target=_sat_worker, args=(queue, n, timeout, optimize, encoding))
    p.daemon = True
    p.start()
    p.join(timeout)

    last_result = None
    while not queue.empty():
        last_result = queue.get()

    if p.is_alive():
        p.terminate()
        p.join()
        if last_result is not None:
            return timeout, last_result[1], last_result[2], last_result[3]
        else:
            return timeout, False, None, None
    else:
        if last_result is not None:
            return last_result
        else:
            return timeout, False, None, None