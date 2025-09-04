def generate_smtlib(n: int):
    """
    Generate SMT-lib content for the decision version of tournament scheduling
    """
    
    weeks = n - 1
    periods = n // 2
    
    smt_content = []
    
    # Header
    smt_content.append("; Tournament scheduling - Decision problem")
    smt_content.append(f"; Teams: {n}, Weeks: {weeks}, Periods: {periods}")
    smt_content.append("")
    
    # Logic
    smt_content.append("(set-info :smt-lib-version 2.6)")
    smt_content.append("(set-logic QF_LIA)")
    smt_content.append("(set-option :produce-models true)")
    smt_content.append("")
    
    # Declare variables for each match (i,j) where i < j
    smt_content.append("; Variables for match scheduling")
    smt_content.append("; M_i_j: week when team i plays team j")
    smt_content.append("; P_i_j: period when team i plays team j")
    
    for i in range(n):
        for j in range(i + 1, n):
            smt_content.append(f"(declare-fun M_{i}_{j} () Int)")
            smt_content.append(f"(declare-fun P_{i}_{j} () Int)")
    
    smt_content.append("")
    
    # Domain constraints
    smt_content.append("; Domain constraints: 0 <= M < weeks, 0 <= P < periods")
    for i in range(n):
        for j in range(i + 1, n):
            smt_content.append(f"(assert (and (>= M_{i}_{j} 0) (< M_{i}_{j} {weeks})))")
            smt_content.append(f"(assert (and (>= P_{i}_{j} 0) (< P_{i}_{j} {periods})))")
    
    smt_content.append("")
    
    # Constraint 1: Every team plays exactly once per week
    smt_content.append("; Constraint 1: Each team plays exactly once per week")
    for team in range(n):
        for week in range(weeks):
            # Count matches for this team in this week
            matches_in_week = []
            for i in range(n):
                for j in range(i + 1, n):
                    if team == i or team == j:
                        matches_in_week.append(f"(ite (= M_{i}_{j} {week}) 1 0)")
            
            if matches_in_week:
                sum_expr = matches_in_week[0] if len(matches_in_week) == 1 else f"(+ {' '.join(matches_in_week)})"
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
            sum_expr = matches_in_week[0] if len(matches_in_week) == 1 else f"(+ {' '.join(matches_in_week)})"
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
                sum_expr = matches_in_slot[0] if len(matches_in_slot) == 1 else f"(+ {' '.join(matches_in_slot)})"
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
                sum_expr = matches_in_period[0] if len(matches_in_period) == 1 else f"(+ {' '.join(matches_in_period)})"
                smt_content.append(f"(assert (<= {sum_expr} 2))")
    
    smt_content.append("")
    
    # Check satisfiability
    smt_content.append("(check-sat)")
    smt_content.append("(get-model)")
    
    return '\n'.join(smt_content)