def generate_smtlib(n: int):
    """
    Generate SMT-lib content for the optimization version of tournament scheduling
    Minimize the maximum imbalance between home and away games
    """
    
    weeks = n - 1
    periods = n // 2
    
    smt_content = []
    
    # Header
    smt_content.append("; Tournament scheduling - Optimization problem")
    smt_content.append(f"; Teams: {n}, Weeks: {weeks}, Periods: {periods}")
    smt_content.append("; Objective: minimize max home-away imbalance")
    smt_content.append("")
    
    # Logic - Using standard SMT-lib 2.6 format
    smt_content.append("(set-info :smt-lib-version 2.6)")
    smt_content.append("(set-logic QF_LIA)")
    smt_content.append("(set-option :produce-models true)")
    smt_content.append("")
    
    # Declare variables for each match (i,j) where i < j
    smt_content.append("; Variables for match scheduling")
    smt_content.append("; M_i_j: week when team i plays team j")
    smt_content.append("; P_i_j: period when team i plays team j")
    smt_content.append("; H_i_j: true if team i is home in match (i,j)")
    
    for i in range(n):
        for j in range(i + 1, n):
            smt_content.append(f"(declare-fun M_{i}_{j} () Int)")
            smt_content.append(f"(declare-fun P_{i}_{j} () Int)")
            smt_content.append(f"(declare-fun H_{i}_{j} () Bool)")
    
    smt_content.append("")
    
    # Variables for home game counting
    smt_content.append("; Home game counters for each team")
    for t in range(n):
        smt_content.append(f"(declare-fun home_count_{t} () Int)")
        smt_content.append(f"(declare-fun balance_{t} () Int)")
        smt_content.append(f"(declare-fun abs_balance_{t} () Int)")
    
    smt_content.append("")
    
    # Objective variable
    smt_content.append("; Objective: maximum absolute balance")
    smt_content.append("(declare-fun max_abs_balance () Int)")
    smt_content.append("")
    
    # Domain constraints
    smt_content.append("; Domain constraints")
    for i in range(n):
        for j in range(i + 1, n):
            smt_content.append(f"(assert (and (>= M_{i}_{j} 0) (< M_{i}_{j} {weeks})))")
            smt_content.append(f"(assert (and (>= P_{i}_{j} 0) (< P_{i}_{j} {periods})))")
    
    smt_content.append("")
    
    # Constraint 1: Every team plays exactly once per week
    smt_content.append("; Constraint 1: Each team plays exactly once per week")
    for team in range(n):
        for week in range(weeks):
            matches_in_week = []
            for i in range(n):
                for j in range(i + 1, n):
                    if team == i or team == j:
                        matches_in_week.append(f"(ite (= M_{i}_{j} {week}) 1 0)")
            
            if matches_in_week:
                sum_expr = build_sum_expr(matches_in_week)
                smt_content.append(f"(assert (= {sum_expr} 1))")
    
    smt_content.append("")
    
    # Constraint 2: Exactly periods matches per week
    smt_content.append("; Constraint 2: Exactly periods matches per week")
    for week in range(weeks):
        matches_in_week = []
        for i in range(n):
            for j in range(i + 1, n):
                matches_in_week.append(f"(ite (= M_{i}_{j} {week}) 1 0)")
        
        if matches_in_week:
            sum_expr = build_sum_expr(matches_in_week)
            smt_content.append(f"(assert (= {sum_expr} {periods}))")
    
    smt_content.append("")
    
    # Constraint 3: Exactly one match per week-period combination
    smt_content.append("; Constraint 3: One match per week-period slot")
    for week in range(weeks):
        for period in range(periods):
            matches_in_slot = []
            for i in range(n):
                for j in range(i + 1, n):
                    matches_in_slot.append(f"(ite (and (= M_{i}_{j} {week}) (= P_{i}_{j} {period})) 1 0)")
            
            if matches_in_slot:
                sum_expr = build_sum_expr(matches_in_slot)
                smt_content.append(f"(assert (= {sum_expr} 1))")
    
    smt_content.append("")
    
    # Constraint 4: Each team plays in each period at most twice
    smt_content.append("; Constraint 4: Each team in each period at most twice")
    for team in range(n):
        for period in range(periods):
            matches_in_period = []
            for i in range(n):
                for j in range(i + 1, n):
                    if team == i or team == j:
                        matches_in_period.append(f"(ite (= P_{i}_{j} {period}) 1 0)")
            
            if matches_in_period:
                sum_expr = build_sum_expr(matches_in_period)
                smt_content.append(f"(assert (<= {sum_expr} 2))")
    
    smt_content.append("")
    
    # Home game counting constraints
    smt_content.append("; Home game counting")
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
        
        if home_games:
            sum_expr = build_sum_expr(home_games)
            smt_content.append(f"(assert (= home_count_{t} {sum_expr}))")
    
    smt_content.append("")
    
    # Balance calculation: balance = 2 * home_count - weeks
    smt_content.append("; Balance calculation")
    for t in range(n):
        smt_content.append(f"(assert (= balance_{t} (- (* 2 home_count_{t}) {weeks})))")
    
    smt_content.append("")
    
    # Absolute balance calculation
    smt_content.append("; Absolute balance")
    for t in range(n):
        smt_content.append(f"(assert (>= abs_balance_{t} balance_{t}))")
        smt_content.append(f"(assert (>= abs_balance_{t} (- balance_{t})))")
    
    smt_content.append("")
    
    # Maximum absolute balance constraints
    smt_content.append("; Maximum absolute balance")
    smt_content.append("(assert (>= max_abs_balance 0))")
    for t in range(n):
        smt_content.append(f"(assert (>= max_abs_balance abs_balance_{t}))")
    
    smt_content.append("")
    
    # For solvers that support optimization (Z3, MathSAT)
    smt_content.append("; Optimization directive (for solvers that support it)")
    smt_content.append("(minimize max_abs_balance)")
    smt_content.append("")
    
    # For solvers without optimization, we can add a bound and do binary search
    smt_content.append("; Alternative: assert a bound for decision version")
    smt_content.append("; (assert (<= max_abs_balance 1))")
    smt_content.append("")
    
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