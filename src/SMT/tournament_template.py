
def generate_decision1_smt(n: int, timeout_ms: int = 300000) -> str:
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


def generate_decision3_smt(n: int, timeout_ms: int = 300000) -> str:
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


def generate_optimization3_smt(n: int, timeout_ms: int = 300000) -> str:
    """Genera il modello optimization3 in formato SMT-LIB (con minimizzazione)"""
    weeks = n - 1
    periods = n // 2
    
    smt = []
    smt.append(f"; Tournament scheduling - Optimization problem 3")
    smt.append(f"; n={n}, weeks={weeks}, periods={periods}")
    smt.append("")
    smt.append("(set-option :produce-models true)")
    smt.append(f"(set-option :timeout {timeout_ms})")
    smt.append("(set-logic QF_LIA)")
    smt.append("")
    
    # Dichiarazione variabili
    smt.append("; Match variables")
    for i in range(n):
        for j in range(n):
            if i != j:
                smt.append(f"(declare-fun M_{i}_{j} () Int)")
                smt.append(f"(declare-fun P_{i}_{j} () Int)")
                smt.append(f"(declare-fun H_{i}_{j} () Bool)")
    
    smt.append("")
    smt.append("; Objective variables")
    for t in range(n):
        smt.append(f"(declare-fun home_count_{t} () Int)")
        smt.append(f"(declare-fun balance_{t} () Int)")
        smt.append(f"(declare-fun abs_balance_{t} () Int)")
    smt.append("(declare-fun max_abs_balance () Int)")
    
    # Vincoli come nel decision3
    smt.append("")
    smt.append("; Domain constraints")
    for i in range(n):
        for j in range(n):
            if i != j:
                smt.append(f"(assert (and (>= M_{i}_{j} 0) (< M_{i}_{j} {weeks})))")
                smt.append(f"(assert (and (>= P_{i}_{j} 0) (< P_{i}_{j} {periods})))")
    
    smt.append("")
    smt.append("; Symmetry constraints")
    for i in range(n):
        for j in range(i+1, n):
            smt.append(f"(assert (= M_{i}_{j} M_{j}_{i}))")
            smt.append(f"(assert (= P_{i}_{j} P_{j}_{i}))")
            smt.append(f"(assert (= H_{i}_{j} (not H_{j}_{i})))")
    
    # Vincoli del torneo (1-4)
    smt.append("")
    smt.append("; Tournament constraints")
    
    # Constraint 1
    for team in range(n):
        for w in range(weeks):
            terms = []
            for i in range(n):
                for j in range(n):
                    if i < j and (team == i or team == j):
                        terms.append(f"(ite (= M_{i}_{j} {w}) 1 0)")
            if terms:
                smt.append(f"(assert (= (+ {' '.join(terms)}) 1))")
    
    # Constraint 2
    for w in range(weeks):
        terms = []
        for i in range(n):
            for j in range(i+1, n):
                terms.append(f"(ite (= M_{i}_{j} {w}) 1 0)")
        smt.append(f"(assert (= (+ {' '.join(terms)}) {periods}))")
    
    # Constraint 3
    for w in range(weeks):
        for p in range(periods):
            terms = []
            for i in range(n):
                for j in range(i+1, n):
                    terms.append(f"(ite (and (= M_{i}_{j} {w}) (= P_{i}_{j} {p})) 1 0)")
            smt.append(f"(assert (= (+ {' '.join(terms)}) 1))")
    
    # Constraint 4
    for team in range(n):
        for p in range(periods):
            terms = []
            for i in range(n):
                for j in range(i+1, n):
                    if team == i or team == j:
                        terms.append(f"(ite (= P_{i}_{j} {p}) 1 0)")
            if terms:
                smt.append(f"(assert (<= (+ {' '.join(terms)}) 2))")
    
    # Vincoli obiettivo
    smt.append("")
    smt.append("; Objective constraints")
    
    # home_count[t] = sum of home games for team t
    for t in range(n):
        terms = []
        for u in range(n):
            if u != t:
                terms.append(f"(ite H_{t}_{u} 1 0)")
        if terms:
            smt.append(f"(assert (= home_count_{t} (+ {' '.join(terms)})))")
    
    # balance[t] = 2 * home_count[t] - weeks
    for t in range(n):
        smt.append(f"(assert (= balance_{t} (- (* 2 home_count_{t}) {weeks})))")
    
    # abs_balance[t] = |balance[t]|
    for t in range(n):
        smt.append(f"(assert (>= abs_balance_{t} balance_{t}))")
        smt.append(f"(assert (>= abs_balance_{t} (- balance_{t})))")
    
    # max_abs_balance >= abs_balance[t] for all t
    smt.append(f"(assert (>= max_abs_balance 0))")
    for t in range(n):
        smt.append(f"(assert (>= max_abs_balance abs_balance_{t}))")
    
    smt.append("")
    smt.append("; Minimize max_abs_balance")
    smt.append("(minimize max_abs_balance)")
    smt.append("")
    smt.append("(check-sat)")
    smt.append("(get-model)")
    smt.append("(get-objectives)")
    smt.append("(exit)")
    
    return '\n'.join(smt)


def save_smt_file(content: str, filename: str):
    """Salva il contenuto SMT-LIB in un file"""
    with open(filename, 'w') as f:
        f.write(content)