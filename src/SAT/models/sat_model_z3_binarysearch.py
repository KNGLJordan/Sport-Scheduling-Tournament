from z3 import *
from itertools import combinations
import time
import numpy as np
import math

def at_least_one_seq(bool_vars):
    return Or(bool_vars)

def at_most_one_seq(bool_vars, name):
    constraints = []
    n = len(bool_vars)
    s = [Bool(f"s_{name}_{i}") for i in range(n - 1)]
    constraints.append(Or(Not(bool_vars[0]), s[0]))
    constraints.append(Or(Not(bool_vars[-1]), Not(s[-1])))
    for i in range(1, n - 1):
        constraints.append(Or(Not(bool_vars[i]), s[i]))
        constraints.append(Or(Not(bool_vars[i]), Not(s[i - 1])))
        constraints.append(Or(Not(s[i - 1]), s[i]))
    return And(constraints)

def exactly_one_seq(bool_vars, name):
    return And(at_least_one_seq(bool_vars), at_most_one_seq(bool_vars, name))

def at_most_k_seq(bool_vars, k, name):
    constraints = []
    n = len(bool_vars)
    s = [[Bool(f"s_{name}_{i}_{j}") for j in range(k)] for i in range(n - 1)]
    constraints.append(Or(Not(bool_vars[0]), s[0][0]))
    constraints += [Not(s[0][j]) for j in range(1, k)]
    for i in range(1, n-1):
        constraints.append(Or(Not(bool_vars[i]), s[i][0]))
        constraints.append(Or(Not(s[i-1][0]), s[i][0]))
        constraints.append(Or(Not(bool_vars[i]), Not(s[i-1][k-1])))
        for j in range(1, k):
            constraints.append(Or(Not(bool_vars[i]), Not(s[i-1][j-1]), s[i][j]))
            constraints.append(Or(Not(s[i-1][j]), s[i][j]))
    constraints.append(Or(Not(bool_vars[-1]), Not(s[-1][k-1])))
    return And(constraints)

def at_least_k_seq(bool_vars, k, name):
    return at_most_k_seq([Not(b) for b in bool_vars], len(bool_vars) - k, f"not_{name}")

def sports_scheduling_sat(n, timeout=300):
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

    def build_solver(imbalance):
        s = Solver()
        s.set("timeout", int(timeout * 1000 - (time.time() - start_time) * 1000))

        # 0. Each slot has exactly one home and one away
        for w in range(weeks):
            for p in range(periods):
                s.add(exactly_one_seq([home[t, w, p] for t in teams], name=f"slot_home_{w}_{p}"))
                s.add(exactly_one_seq([away[t, w, p] for t in teams], name=f"slot_away_{w}_{p}"))

        # 1. Every team plays exactly once per week
        for t in teams:
            for w in range(weeks):
                vars_in_week = [home[t, w, p] for p in range(periods)] + \
                               [away[t, w, p] for p in range(periods)]
                s.add(exactly_one_seq(vars_in_week, name=f"team_plays_{t}_{w}"))

        # 2. Every pair meets exactly once
        for i, j in combinations(teams, 2):
            match_slots = []
            for w in range(weeks):
                for p in range(periods):
                    match_slots.append(
                        Or(And(home[i, w, p], away[j, w, p]),
                           And(home[j, w, p], away[i, w, p]))
                    )
            s.add(exactly_one_seq(match_slots, name=f"pair_meets_{i}_{j}"))

        # 3. At most 2 games per team per period
        for t in teams:
            for p in range(periods):
                games = [home[t, w, p] for w in range(weeks)] + [away[t, w, p] for w in range(weeks)]
                s.add(at_most_k_seq(games, 2, name=f"team_{t}_period_{p}"))

        # 4. Home/away balance: each team has home games in [min_home, max_home]
        min_home = (weeks // 2) - imbalance
        max_home = (weeks + 1) // 2 + imbalance
        for t in teams:
            home_games = [home[t, w, p] for w in range(weeks) for p in range(periods)]
            s.add(at_least_k_seq(home_games, min_home, f"home_min_{t}"))
            s.add(at_most_k_seq(home_games, max_home, f"home_max_{t}"))

        return s

    low, high = 0, weeks // 2
    best_model = None
    best_imbalance = None

    while low <= high and (time.time() - start_time) < timeout:
        mid = (low + high) // 2
        s = build_solver(mid)
        if s.check() == sat:
            best_model = s.model()
            best_imbalance = mid
            high = mid - 1
        else:
            low = mid + 1

    elapsed = time.time() - start_time
    if best_model is None:
        # No solution found
        return elapsed, False, None, None

    # Extract schedule from best_model
    sched = [[None] * weeks for _ in range(periods)]
    for w in range(weeks):
        for p in range(periods):
            home_team = None
            away_team = None
            for i in teams:
                if is_true(best_model.evaluate(home[i, w, p], model_completion=True)):
                    home_team = i + 1
                if is_true(best_model.evaluate(away[i, w, p], model_completion=True)):
                    away_team = i + 1
            sched[p][w] = [home_team, away_team]

    return elapsed, True, best_imbalance, sched