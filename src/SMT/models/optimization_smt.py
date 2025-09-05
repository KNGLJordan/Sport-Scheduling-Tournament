def generate_smtlib(n: int):
    
    weeks = n - 1
    periods = n // 2
    
    smt_content = []
    
    # Logic
    smt_content.append("(set-option :produce-models true)")
    smt_content.append("(set-logic QF_LIA)")
    
    for i in range(n):
        for j in range(i + 1, n):
            smt_content.append(f"(declare-fun W_{i}_{j} () Int)")
            smt_content.append(f"(declare-fun P_{i}_{j} () Int)")
            smt_content.append(f"(declare-fun H_{i}_{j} () Bool)")
    
    # Variables for home game counting
    for t in range(n):
        smt_content.append(f"(declare-fun home_count_{t} () Int)")
        smt_content.append(f"(declare-fun balance_{t} () Int)")
        smt_content.append(f"(declare-fun abs_balance_{t} () Int)")
    
    # Objective variable
    smt_content.append("; Objective: maximum absolute balance")
    smt_content.append("(declare-fun max_abs_balance () Int)")
    
    # Domain constraints
    for i in range(n):
        for j in range(i + 1, n):
            smt_content.append(f"(assert (and (>= W_{i}_{j} 0) (< W_{i}_{j} {weeks})))")
            smt_content.append(f"(assert (and (>= P_{i}_{j} 0) (< P_{i}_{j} {periods})))")
    
    # Constraint 1: Every team plays exactly once per week
    for team in range(n):
        for week in range(weeks):
            matches_in_week = []
            for i in range(n):
                for j in range(i + 1, n):
                    if team == i or team == j:
                        matches_in_week.append(f"(ite (= W_{i}_{j} {week}) 1 0)")
            
            sum_expr = build_sum_expr(matches_in_week)
            smt_content.append(f"(assert (= {sum_expr} 1))")
    
    # Constraint 2: Exactly periods matches per week
    for week in range(weeks):
        matches_in_week = []
        for i in range(n):
            for j in range(i + 1, n):
                matches_in_week.append(f"(ite (= W_{i}_{j} {week}) 1 0)")
        
        sum_expr = build_sum_expr(matches_in_week)
        smt_content.append(f"(assert (= {sum_expr} {periods}))")
    
    # Constraint 3: Exactly one match per week-period combination
    for week in range(weeks):
        for period in range(periods):
            matches_in_slot = []
            for i in range(n):
                for j in range(i + 1, n):
                    matches_in_slot.append(f"(ite (and (= W_{i}_{j} {week}) (= P_{i}_{j} {period})) 1 0)")
            
            sum_expr = build_sum_expr(matches_in_slot)
            smt_content.append(f"(assert (= {sum_expr} 1))")
    
    # Constraint 4: Each team plays in each period at most twice
    for team in range(n):
        for period in range(periods):
            matches_in_period = []
            for i in range(n):
                for j in range(i + 1, n):
                    if team == i or team == j:
                        matches_in_period.append(f"(ite (= P_{i}_{j} {period}) 1 0)")
            
            sum_expr = build_sum_expr(matches_in_period)
            smt_content.append(f"(assert (<= {sum_expr} 2))")
    
    # Home game counting constraints
    for t in range(n):
        home_games = []
        for i in range(n):
            for j in range(i + 1, n):
                if t == i:
                    # Team t is i, home if H_i_j is true
                    home_games.append(f"(ite H_{i}_{j} 1 0)")
                elif t == j:
                    # Team t is j, home if H_i_j is false
                    home_games.append(f"(ite (not H_{i}_{j}) 1 0)")

        sum_expr = build_sum_expr(home_games)
        smt_content.append(f"(assert (= home_count_{t} {sum_expr}))")

    # Balance calculation: balance = 2 * home_count - weeks
    for t in range(n):
        smt_content.append(f"(assert (= balance_{t} (- (* 2 home_count_{t}) {weeks})))")
    
    # Absolute balance calculation
    for t in range(n):
        smt_content.append(f"(assert (>= abs_balance_{t} balance_{t}))")
        smt_content.append(f"(assert (>= abs_balance_{t} (- balance_{t})))")
    
    # Maximum absolute balance constraints
    smt_content.append("(assert (>= max_abs_balance 0))")
    for t in range(n):
        smt_content.append(f"(assert (>= max_abs_balance abs_balance_{t}))")
    
    # For solvers that support optimization (Z3, MathSAT)
    smt_content.append("; Optimization directive (for solvers that support it)")
    smt_content.append("(minimize max_abs_balance)")
    
    # For solvers without optimization, we can add a bound and do binary search
    smt_content.append("; Alternative: assert a bound for decision version")
    smt_content.append("; (assert (<= max_abs_balance 1))")
    
    # Check and get model
    smt_content.append("(check-sat)")
    smt_content.append("(get-model)")
    smt_content.append("; (get-objectives)")  # For solvers that support it
    
    return '\n'.join(smt_content)

def build_sum_expr(terms):
    """
    Build a sum expression from a list of terms
    Handles the case where there's only one term
    """
    if not terms:
        return "0"
    elif len(terms) == 1:
        return terms[0]
    else:
        # Build nested additions for compatibility
        result = terms[0]
        for term in terms[1:]:
            result = f"(+ {result} {term})"
        return result