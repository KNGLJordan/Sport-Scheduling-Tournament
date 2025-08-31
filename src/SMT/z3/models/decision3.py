from z3 import *
import time

def get_solution(n: int, model):
    """
    Restituisce la soluzione come lista di liste di liste:
    sol[period][week] = [team1, team2]
    """
    weeks = n - 1
    periods = n // 2
    matches = [(i, j) for i in range(n) for j in range(n) if i!=j] #rectangle instead of triangle

    # Ricostruisco le variabili come in solve_instance
    M = {(t1, t2): Int(f"M_{t1}_{t2}") for (t1, t2) in matches}
    P = {(t1, t2): Int(f"P_{t1}_{t2}") for (t1, t2) in matches}
    H = {(t1, t2): Bool(f"H_{t1}_{t2}") for (t1, t2) in matches} #home team

    # Struttura della soluzione: periods × weeks
    solution = [[None for _ in range(weeks)] for _ in range(periods)]

    # print(model[M[(t1, t2)]].as_long() for (t1, t2) in matches)

    for (t1, t2) in matches:
        w = model[M[(t1, t2)]].as_long()
        p = model[P[(t1, t2)]].as_long()
        h = is_true(model[H[(t1, t2)]])

        if h:
            solution[p][w] = [t1 + 1, t2 + 1]

   # print(solution)
    
    return solution

def solve_instance(n: int, 
                   time_limit: int, 
                   seed: int, 
                   print_solution: bool = False):
    
    # ------------------------------- MODEL ----------------------------------

    weeks = n - 1
    periods = n // 2

    matches = [(i, j) for i in range(n) for j in range(n) if i!=j] #rectangle instead of triangle

    M = {(t1, t2): Int(f"M_{t1}_{t2}") for (t1, t2) in matches}
    P = {(t1, t2): Int(f"P_{t1}_{t2}") for (t1, t2) in matches}
    H = {(t1, t2): Bool(f"H_{t1}_{t2}") for (t1, t2) in matches} #home team


    s = Solver()
    for (t1, t2) in matches:
        s.add(M[(t1, t2)] >= 0, M[(t1, t2)] < weeks)
        s.add(P[(t1, t2)] >= 0, P[(t1, t2)] < periods)
    #define the values that the Weeks matrix and the Periods matrix and Home martix can assume (between 0 and weeks-1 or periods-1 or 0 and 1)

    # 0. M[i,j] must be equal to M[j,i] and P[i,j] must be equal to P[j,i] and H[i,j] must be Not(H[j,i])
    for (t1, t2) in matches:
        if t1 < t2:
            s.add(M[(t1, t2)] == M[(t2, t1)])
            s.add(P[(t1, t2)] == P[(t2, t1)])
            s.add(H[(t1, t2)] == Not(H[(t2, t1)]))

    # 1. Every team plays once a week
    for team in range(n):
        for w in range(weeks):
            s.add(Sum([If(M[(t1, t2)] == w, 1, 0)
                    for (t1, t2) in matches if team in (t1, t2) and t1<t2]) == 1) 

    # from itertools import combinations
    # pairs = list(combinations(range(n), 2))
    # pairs_by_team = {t: [p for p in pairs if t in p] for t in range(n)}

    # for team in range(n):
    #     team_pairs = pairs_by_team[team]
    #     # domain already restricted to 0..weeks-1 elsewhere
    #     s.add(Distinct([M[p] for p in team_pairs]))

    

    # 2. Every week have exactly periods match
    for w in range(weeks):
        s.add(Sum([If(M[(t1, t2)] == w, 1, 0) for (t1, t2) in matches if t1<t2]) == periods)

    # 3. Every week and period have exactly one match
    for w in range(weeks):
        for p in range(periods):
            s.add(Sum([If(And(M[(t1, t2)] == w, P[(t1, t2)] == p), 1, 0)
                    for (t1, t2) in matches if t1<t2]) == 1)

    # 4. Every team can have a match in the same period at most two times
    for team in range(n):
        for p in range(periods):
            s.add(Sum([If(P[(t1, t2)] == p, 1, 0)
                    for (t1, t2) in matches if team in (t1, t2) and t1<t2]) <= 2)
            
    # IMPLIED & SYMMETRY BREAKING
    # ...

    # ------------------------------- SOLVING ----------------------------------
    
    s.set("timeout", time_limit * 1000, "random_seed", seed)
    
    start = time.time()
    result = s.check()
    elapsed = time.time() - start

    if result == sat:

        sol = get_solution(n, s.model())

        # obj none if is a decision problem
        obj = None
        # optimal true if instance is solved for the decision problem
        optimal = True

        print(f"\t\tSolution found in {elapsed:.1f}s.")
        return elapsed, optimal, obj, sol
    elif result == unsat:
        print("\t\tSolution not found.")
        return elapsed, False, None, None
    else:
        print("\t\tTimeout reached.")
        return elapsed, False, None, None

    # if result == sat:
    #     model = s.model()
    #     # Tabella [field][week]
    #     schedule = [["" for _ in range(weeks)] for _ in range(periods)]
    #     for (t1, t2) in matches:
    #         w = model[M[(t1, t2)]].as_long()
    #         f = model[P[(t1, t2)]].as_long()
    #         schedule[f][w] = f"[{t1+1}, {t2+1}]"

    #     # Stampa intestazione (settimane)
    #     col_width = 8
    #     header = " " * (col_width-1) + "".join(str(w+1).center(col_width) for w in range(weeks))
    #     print(header)
    #     # Stampa righe (campi)
    #     for f in range(periods):
    #         row = str(f+1).ljust(col_width-1)
    #         for w in range(weeks):
    #             row += schedule[f][w].ljust(col_width)
    #         print(row)
    #     print(f"\nTempo di risoluzione: {elapsed:.3f} secondi")

    # else:
    #     print("Nessuna soluzione trovata.")
    #     print(f"Tempo di risoluzione: {elapsed:.3f} secondi")


