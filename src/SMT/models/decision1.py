from z3 import *
import time

def get_solution(n: int, model):
    """
    Restituisce la soluzione come lista di liste di liste:
    sol[period][week] = [team1, team2]
    """
    weeks = n - 1
    periods = n // 2
    matches = [(i, j) for i in range(n) for j in range(i+1, n)]

    # Ricostruisco le variabili come in solve_instance
    M = {(t1, t2): Int(f"M_{t1}_{t2}") for (t1, t2) in matches}
    P = {(t1, t2): Int(f"P_{t1}_{t2}") for (t1, t2) in matches}

    # Struttura della soluzione: periods × weeks
    solution = [[None for _ in range(weeks)] for _ in range(periods)]

    for (t1, t2) in matches:
        w = model[M[(t1, t2)]].as_long()
        p = model[P[(t1, t2)]].as_long()
        solution[p][w] = [t1 + 1, t2 + 1]  # squadre numerate da 1

    return solution

def solve_instance(n: int, 
                   time_limit: int, 
                   seed: int, 
                   print_solution: bool = False):
    
    # ------------------------------- MODEL ----------------------------------

    weeks = n - 1
    periods = n // 2

    matches = [(i, j) for i in range(n) for j in range(i+1, n)]

    M = {(t1, t2): Int(f"M_{t1}_{t2}") for (t1, t2) in matches}
    P = {(t1, t2): Int(f"P_{t1}_{t2}") for (t1, t2) in matches}

    s = Solver()
    for (t1, t2) in matches:
        s.add(M[(t1, t2)] >= 0, M[(t1, t2)] < weeks)
        s.add(P[(t1, t2)] >= 0, P[(t1, t2)] < periods)

    # 1. Every team plays once a week
    for team in range(n):
        for w in range(weeks):
            s.add(Sum([If(M[(t1, t2)] == w, 1, 0)
                    for (t1, t2) in matches if team in (t1, t2)]) == 1)

    # 2. Every week have exactly periods match
    for w in range(weeks):
        s.add(Sum([If(M[(t1, t2)] == w, 1, 0) for (t1, t2) in matches]) == periods)

    # 3. Every week and period have exactly one match
    for w in range(weeks):
        for f in range(periods):
            s.add(Sum([If(And(M[(t1, t2)] == w, P[(t1, t2)] == f), 1, 0)
                    for (t1, t2) in matches]) == 1)

    # 4. Every team can have a match in the same period at most two times
    for team in range(n):
        for f in range(periods):
            s.add(Sum([If(P[(t1, t2)] == f, 1, 0)
                    for (t1, t2) in matches if team in (t1, t2)]) <= 2)
            
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


