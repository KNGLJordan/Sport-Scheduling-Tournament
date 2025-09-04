
def generate_decision1_smt(n: int, timeout_ms: int, solver: str) -> str:
    """Genera il modello decision1 in formato SMT-LIB"""
    weeks = n - 1
    periods = n // 2
    
    smt = []
    smt.append(f"; Tournament scheduling - Decision problem 1")
    smt.append(f"; n={n}, weeks={weeks}, periods={periods}")
    smt.append("")
    smt.append("(set-option :produce-models true)")
    smt.append(f"(set-option :timeout {timeout_ms})")
    smt.append("(set-logic QF_LIA)")
    smt.append("")
    
    # Dichiarazione variabili M[i,j] e P[i,j] per ogni coppia di squadre
    smt.append("; Variables M[i,j] - week when team i plays team j")
    smt.append("; Variables P[i,j] - period when team i plays team j")
    for i in range(n):
        for j in range(i+1, n):
            smt.append(f"(declare-fun M_{i}_{j} () Int)")
            smt.append(f"(declare-fun P_{i}_{j} () Int)")
    
    smt.append("")
    smt.append("; Domain constraints")
    for i in range(n):
        for j in range(i+1, n):
            smt.append(f"(assert (and (>= M_{i}_{j} 0) (< M_{i}_{j} {weeks})))")
            smt.append(f"(assert (and (>= P_{i}_{j} 0) (< P_{i}_{j} {periods})))")
    
    smt.append("")
    smt.append("; Constraint 1: Every team plays once a week")
    for team in range(n):
        for w in range(weeks):
            terms = []
            for i in range(n):
                for j in range(i+1, n):
                    if team == i or team == j:
                        terms.append(f"(ite (= M_{i}_{j} {w}) 1 0)")
            if terms:
                smt.append(f"(assert (= (+ {' '.join(terms)}) 1))")
    
    smt.append("")
    smt.append("; Constraint 2: Every week has exactly periods matches")
    for w in range(weeks):
        terms = []
        for i in range(n):
            for j in range(i+1, n):
                terms.append(f"(ite (= M_{i}_{j} {w}) 1 0)")
        smt.append(f"(assert (= (+ {' '.join(terms)}) {periods}))")
    
    smt.append("")
    smt.append("; Constraint 3: Every week and period have exactly one match")
    for w in range(weeks):
        for p in range(periods):
            terms = []
            for i in range(n):
                for j in range(i+1, n):
                    terms.append(f"(ite (and (= M_{i}_{j} {w}) (= P_{i}_{j} {p})) 1 0)")
            smt.append(f"(assert (= (+ {' '.join(terms)}) 1))")
    
    smt.append("")
    smt.append("; Constraint 4: Every team can have a match in the same period at most two times")
    for team in range(n):
        for p in range(periods):
            terms = []
            for i in range(n):
                for j in range(i+1, n):
                    if team == i or team == j:
                        terms.append(f"(ite (= P_{i}_{j} {p}) 1 0)")
            if terms:
                smt.append(f"(assert (<= (+ {' '.join(terms)}) 2))")
    
    smt.append("")
    smt.append("(check-sat)")
    smt.append("(get-model)")
    smt.append("(exit)")
    
    return '\n'.join(smt)


def generate_decision3_smt(n: int, timeout_ms: int, solver:str) -> str:
    """Genera il modello decision3 in formato SMT-LIB (con home/away)"""
    weeks = n - 1
    periods = n // 2
    
    smt = []
    smt.append(f"; Tournament scheduling - Decision problem 3 (with home/away)")
    smt.append(f"; n={n}, weeks={weeks}, periods={periods}")
    smt.append("")
    smt.append("(set-option :produce-models true)")
    smt.append(f"(set-option :timeout {timeout_ms})")
    smt.append("(set-logic QF_LIA)")
    smt.append("")
    
    # Dichiarazione variabili per il rettangolo completo (i != j)
    smt.append("; Variables M[i,j], P[i,j], H[i,j] for all i!=j")
    for i in range(n):
        for j in range(n):
            if i != j:
                smt.append(f"(declare-fun M_{i}_{j} () Int)")
                smt.append(f"(declare-fun P_{i}_{j} () Int)")
                smt.append(f"(declare-fun H_{i}_{j} () Bool)")
    
    smt.append("")
    smt.append("; Domain constraints")
    for i in range(n):
        for j in range(n):
            if i != j:
                smt.append(f"(assert (and (>= M_{i}_{j} 0) (< M_{i}_{j} {weeks})))")
                smt.append(f"(assert (and (>= P_{i}_{j} 0) (< P_{i}_{j} {periods})))")
    
    smt.append("")
    smt.append("; Constraint 0: Symmetry - M[i,j] = M[j,i], P[i,j] = P[j,i], H[i,j] = not H[j,i]")
    for i in range(n):
        for j in range(i+1, n):
            smt.append(f"(assert (= M_{i}_{j} M_{j}_{i}))")
            smt.append(f"(assert (= P_{i}_{j} P_{j}_{i}))")
            smt.append(f"(assert (= H_{i}_{j} (not H_{j}_{i})))")
    
    smt.append("")
    smt.append("; Constraint 1: Every team plays once a week")
    for team in range(n):
        for w in range(weeks):
            terms = []
            for i in range(n):
                for j in range(n):
                    if i < j and (team == i or team == j):
                        terms.append(f"(ite (= M_{i}_{j} {w}) 1 0)")
            if terms:
                smt.append(f"(assert (= (+ {' '.join(terms)}) 1))")
    
    smt.append("")
    smt.append("; Constraint 2: Every week has exactly periods matches")
    for w in range(weeks):
        terms = []
        for i in range(n):
            for j in range(i+1, n):
                terms.append(f"(ite (= M_{i}_{j} {w}) 1 0)")
        smt.append(f"(assert (= (+ {' '.join(terms)}) {periods}))")
    
    smt.append("")
    smt.append("; Constraint 3: Every week and period have exactly one match")
    for w in range(weeks):
        for p in range(periods):
            terms = []
            for i in range(n):
                for j in range(i+1, n):
                    terms.append(f"(ite (and (= M_{i}_{j} {w}) (= P_{i}_{j} {p})) 1 0)")
            smt.append(f"(assert (= (+ {' '.join(terms)}) 1))")
    
    smt.append("")
    smt.append("; Constraint 4: Every team can have a match in the same period at most two times")
    for team in range(n):
        for p in range(periods):
            terms = []
            for i in range(n):
                for j in range(i+1, n):
                    if team == i or team == j:
                        terms.append(f"(ite (= P_{i}_{j} {p}) 1 0)")
            if terms:
                smt.append(f"(assert (<= (+ {' '.join(terms)}) 2))")
    
    smt.append("")
    smt.append("(check-sat)")
    smt.append("(get-model)")
    smt.append("(exit)")
    
    return '\n'.join(smt)


def generate_optimization3_smt(n: int, timeout_ms: int, solver:str) -> str:
    """
    Genera il modello optimization3 SMT-LIB compatibile con Z3 e cvc5.
    solver: "z3" o "cvc5".
    Nota: per cvc5 puoi comunque passare il timeout via CLI (es. `cvc5 --tlimit=60 file.smt2`).
    """
    assert solver in ("z3", "cvc5")

    weeks = n - 1
    periods = n // 2

    smt = []
    smt.append(f"; Tournament scheduling - Optimization problem 3")
    smt.append(f"; n={n}, weeks={weeks}, periods={periods}")
    smt.append("")
    smt.append("(set-option :produce-models true)")
    # timeout in ms: Z3 interpreta (set-option :timeout <ms>), cvc5 può ignorarlo;
    # per cvc5 è più affidabile usare l'opzione CLI --tlimit.
    smt.append(f"(set-option :timeout {timeout_ms})")
    smt.append("(set-logic QF_LIA)")
    smt.append("")

    # cvc5: abilita modalità ottimizzazione (deve essere impostata prima del minimize)
    if solver == "cvc5":
        smt.append("; cvc5: attiva modalità ottimizzazione (box = parellel/boxed optimization mode)")
        smt.append("(set-option :opt.priority box)")
        smt.append("")

    # --- declare match variables (i != j) ---
    smt.append("; Match variables")
    for i in range(n):
        for j in range(n):
            if i != j:
                smt.append(f"(declare-fun M_{i}_{j} () Int)")
                smt.append(f"(declare-fun P_{i}_{j} () Int)")
                smt.append(f"(declare-fun H_{i}_{j} () Bool)")

    smt.append("")
    # --- objective helper vars ---
    smt.append("; Objective variables")
    for t in range(n):
        smt.append(f"(declare-fun home_count_{t} () Int)")
        smt.append(f"(declare-fun balance_{t} () Int)")
        smt.append(f"(declare-fun abs_balance_{t} () Int)")
    smt.append("(declare-fun max_abs_balance () Int)")
    smt.append("")

    # --- domain constraints ---
    smt.append("; Domain constraints")
    for i in range(n):
        for j in range(n):
            if i != j:
                smt.append(f"(assert (and (>= M_{i}_{j} 0) (< M_{i}_{j} {weeks})))")
                smt.append(f"(assert (and (>= P_{i}_{j} 0) (< P_{i}_{j} {periods})))")
    smt.append("")

    # --- symmetry constraints (i<j) ---
    smt.append("; Symmetry constraints")
    for i in range(n):
        for j in range(i+1, n):
            smt.append(f"(assert (= M_{i}_{j} M_{j}_{i}))")
            smt.append(f"(assert (= P_{i}_{j} P_{j}_{i}))")
            smt.append(f"(assert (= H_{i}_{j} (not H_{j}_{i})))")
    smt.append("")

    # --- Tournament constraints (1..4) ---
    smt.append("; Tournament constraints")

    # Constraint 1: ogni squadra gioca una volta per settimana
    for team in range(n):
        for w in range(weeks):
            terms = []
            for i in range(n):
                for j in range(i+1, n):
                    if team == i or team == j:
                        terms.append(f"(ite (= M_{i}_{j} {w}) 1 0)")
            if terms:
                smt.append(f"(assert (= (+ {' '.join(terms)}) 1))")
    smt.append("")

    # Constraint 2: ogni settimana ha esattamente 'periods' partite
    for w in range(weeks):
        terms = []
        for i in range(n):
            for j in range(i+1, n):
                terms.append(f"(ite (= M_{i}_{j} {w}) 1 0)")
        smt.append(f"(assert (= (+ {' '.join(terms)}) {periods}))")
    smt.append("")

    # Constraint 3: ogni settimana/periodo ha esattamente una partita
    for w in range(weeks):
        for p in range(periods):
            terms = []
            for i in range(n):
                for j in range(i+1, n):
                    terms.append(f"(ite (and (= M_{i}_{j} {w}) (= P_{i}_{j} {p})) 1 0)")
            smt.append(f"(assert (= (+ {' '.join(terms)}) 1))")
    smt.append("")

    # Constraint 4: per ogni squadra, in ogni periodo al massimo 2 partite
    for team in range(n):
        for p in range(periods):
            terms = []
            for i in range(n):
                for j in range(i+1, n):
                    if team == i or team == j:
                        terms.append(f"(ite (= P_{i}_{j} {p}) 1 0)")
            if terms:
                smt.append(f"(assert (<= (+ {' '.join(terms)}) 2))")
    smt.append("")

    # --- Objective constraints ---
    smt.append("; Objective constraints")
    # home_count[t] = sum(ite H_t_u 1 0) per u != t
    for t in range(n):
        terms = [f"(ite H_{t}_{u} 1 0)" for u in range(n) if u != t]
        if terms:
            smt.append(f"(assert (= home_count_{t} (+ {' '.join(terms)})))")
    smt.append("")

    # balance and absolute balance
    for t in range(n):
        smt.append(f"(assert (= balance_{t} (- (* 2 home_count_{t}) {weeks})))")
        smt.append(f"(assert (>= abs_balance_{t} balance_{t}))")
        smt.append(f"(assert (>= abs_balance_{t} (- balance_{t})))")
    smt.append("")

    # max_abs_balance constraints
    smt.append("(assert (>= max_abs_balance 0))")
    for t in range(n):
        smt.append(f"(assert (>= max_abs_balance abs_balance_{t}))")
    smt.append("")

    # --- Optimization command ---
    smt.append("; Minimize max_abs_balance")
    smt.append("(minimize max_abs_balance)")
    smt.append("")
    smt.append("(check-sat)")
    smt.append("(get-model)")
    # valore dell'obiettivo in modo portabile
    smt.append("(get-value (max_abs_balance))")
    smt.append("(exit)")

    return '\n'.join(smt)


def save_smt_file(content: str, filename: str):
    """Salva il contenuto SMT-LIB in un file"""
    with open(filename, 'w') as f:
        f.write(content)