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

    def build_solver(min_home=None, max_home=None, min_away=None, max_away=None):
        """Builds a solver with the given home game constraints"""
        s = Solver()
        s.set("random_seed", 42)

        # Each slot has exactly one home and one away team
        for w in range(weeks):
            for p in range(periods):
                s.add(exactly_one([home[t, w, p] for t in teams], name=f"slot_home_{w}_{p}"))
                s.add(exactly_one([away[t, w, p] for t in teams], name=f"slot_away_{w}_{p}"))

        # Each team plays exactly once per week (either home or away)
        for t in teams:
            for w in range(weeks):
                vars_in_week = [home[t, w, p] for p in range(periods)] + [away[t, w, p] for p in range(periods)]
                s.add(exactly_one(vars_in_week, name=f"team_plays_{t}_{w}"))

        # Each pair of teams meets exactly once
        for i, j in combinations(teams, 2):
            match_slots = []
            for w in range(weeks):
                for p in range(periods):
                    match_slots.append(
                        Or(And(home[i, w, p], away[j, w, p]),
                           And(home[j, w, p], away[i, w, p]))
                    )
            s.add(exactly_one(match_slots, name=f"pair_meets_{i}_{j}"))

        # No team plays more than twice in any period
        for t in teams:
            for p in range(periods):
                games = [home[t, w, p] for w in range(weeks)] + [away[t, w, p] for w in range(weeks)]
                s.add(at_most_k(games, 2, name=f"team_{t}_period_{p}"))

        # Home/away game constraints for fairness
        if optimize and (min_home is not None and max_home is not None):
            for t in teams:
                home_games = [home[t, w, p] for w in range(weeks) for p in range(periods)]
                s.add(at_least_k(home_games, min_home, name=f"min_home_{t}"))
                s.add(at_most_k(home_games, max_home, name=f"max_home_{t}"))

                #is it necessary to also use the away games constraints?
                #we have to prove that if all teams are constrained to play between, e.g., 1 and 4 home games,
                #there will never be a team that can play 0 or 5 away games, so we can skip this part
                #to prove it mathematically
                """ away_games = [away[t, w, p] for w in range(weeks) for p in range(periods)]
                s.add(at_least_k_seq(away_games, min_away, name=f"min_away_{t}"))
                s.add(at_most_k_seq(away_games, max_away, name=f"max_away_{t}")) """

        num_constraints = len(s.assertions())
        print(f"\tNumber of constraints: {num_constraints}")
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

        # Compute imbalance: home_games - away_games per team
        imbalances = []
        for t in teams:
            home_games = sum(
                1 for w in range(weeks) for p in range(periods)
                if is_true(m.evaluate(home[t, w, p], model_completion=True))
            )
            away_games = sum(
                1 for w in range(weeks) for p in range(periods)
                if is_true(m.evaluate(away[t, w, p], model_completion=True))
            )
            imbalances.append(home_games - away_games)


        obj = max(imbalances) - min(imbalances) - 2
        optimal = (obj == 0 and elapsed < timeout) or (not optimize)

        if not optimize:
            # For decision problem, we return True if feasible, else False. and objective function None
            queue.put((elapsed, optimal, None, sched))
            return True
        else:
            queue.put((elapsed, optimal, obj, sched))
        
        return True



    if optimize:
        # Binary search setup
        min_obj = 0
        max_obj = 2 * n - 4  # Theoretical maximum difference between max and min imbalance
        
        # All possible odd imbalance values (home - away games difference)
        odd_imbalances = list(range(-(n-1), n, 2))
        
        best_model = None
        best_obj = None
        best_sched = None

        # Binary search over possible even objective values
        while min_obj <= max_obj:
            mid = (min_obj + max_obj) // 2
            # Ensure we only test even objective values
            if mid % 2 != 0:
                mid -= 1
                if mid < min_obj:
                    min_obj = mid + 2
                    continue

            print(f"\nTrying objective value: {mid}")

            # Find all possible (max_imb, min_imb) pairs that satisfy max_imb - min_imb == mid
            # and where max_imb > min_imb and both are odd
            temp_max = float('-inf')
            temp_min = float('inf')
            for max_imb in odd_imbalances:
                for min_imb in odd_imbalances:
                    if max_imb >= 0 and min_imb <= 0 and max_imb - min_imb - 2 == mid:
                        temp_max = max(temp_max, max_imb)
                        temp_min = min(temp_min, min_imb)

        #for n=6, when mid=4, an example of possible_pairs would be:
        # 3 - (-3) - 2
        # 1 -(-5) - 2

        #temp_max is used to find the difference between the at_least(home,min_home) and at_most(home,max_home)
        #min_home+max_home=n-1
        #max_home - min_home = temp_max
            for i in range(n):
                for j in range(i+1, n):
                    if i + j == n - 1 and j - i == temp_max:
                        max_home = j
                        min_home = i
                    """ if i + j == n - 1 and j - i == -temp_min:
                        max_away = j
                        min_away = i """

            print(f"  Possible pairs found: max_imb={temp_max}, min_imb={temp_min}")
            print(f"  Max_home= {max_home}, Min_home={min_home}")
           # print(f"  Max_away= {max_away}, Min_away={min_away}")

            first_iteration = False
            if min_home==0 and max_home==n-1:
                #instead of optimising with implied extra constraints, we do the decision problem
                first_iteration = True
            if first_iteration:
                print("  Building the solver in the case where optimization is trivial, and instead therefore we use the decision problem...")
                time_before = time.time()
                decision_problem_feasible()
                time_after = time.time()
                print(f"  Decision problem check completed in {time_after - time_before:.2f} seconds")
                max_obj = mid -2

            else:
                # Build and check the solver
                print("  Building the solver...")
                time_before = time.time()
                s = build_solver(min_home, max_home)
                time_after = time.time()
                print(f"  Solver built in {time_after - time_before:.2f} seconds")

                print("  Checking satisfiability...")
                res = s.check()
                time_after2 = time.time()
                print(f"  Check completed in {time_after2 - time_after:.2f} seconds")

                if res == sat:
                    print("  Found feasible solution")
                    best_model = s.model()
                    best_obj = mid
                    best_sched = extract_schedule(best_model, home, away, teams, weeks, periods)

                    max_obj = mid - 2
            
                else:
                    print("  No solution found, trying higher objective")
                    min_obj = mid + 2

        elapsed = time.time() - start_time
        if best_model is None:
            queue.put((elapsed, False, None, None))
            return

        #we compute best_objective_value as we know: max(imbalances)-min(imbalances)-2
        best_obj = temp_max - temp_min - 2
        optimal = (best_obj == 0 and elapsed < timeout)
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