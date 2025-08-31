"""
Parser per convertire i modelli SMT nel formato di soluzione richiesto
"""

from typing import Dict, List, Optional, Tuple, Any

def parse_tournament_solution(model: Dict[str, Any], n: int, problem_type: str) -> Optional[List[List[List[int]]]]:
    """
    Converte un modello SMT nella struttura di soluzione del torneo
    
    Args:
        model: Dizionario con le assegnazioni delle variabili
        n: Numero di squadre
        problem_type: Tipo di problema ('decision1', 'decision3', 'optimization3')
    
    Returns:
        Soluzione come lista[period][week] = [team1, team2] o None se non valida
    """
    
    if model.get("status") != "sat":
        return None
    
    weeks = n - 1
    periods = n // 2
    
    # Inizializza la struttura della soluzione
    solution = [[None for _ in range(weeks)] for _ in range(periods)]
    
    if problem_type == "decision1":
        # Per decision1: usa solo il triangolo superiore
        for i in range(n):
            for j in range(i+1, n):
                m_key = f"M_{i}_{j}"
                p_key = f"P_{i}_{j}"
                
                if m_key in model and p_key in model:
                    week = model[m_key]
                    period = model[p_key]
                    
                    if 0 <= week < weeks and 0 <= period < periods:
                        solution[period][week] = [i + 1, j + 1]  # Teams numbered from 1
    
    elif problem_type in ["decision3", "optimization3"]:
        # Per decision3 e optimization3: usa il rettangolo completo con home/away
        for i in range(n):
            for j in range(n):
                if i != j:
                    m_key = f"M_{i}_{j}"
                    p_key = f"P_{i}_{j}"
                    h_key = f"H_{i}_{j}"
                    
                    if m_key in model and p_key in model and h_key in model:
                        week = model[m_key]
                        period = model[p_key]
                        is_home = model[h_key]
                        
                        # Aggiungi alla soluzione solo se i è la squadra di casa
                        if is_home and 0 <= week < weeks and 0 <= period < periods:
                            if solution[period][week] is None:
                                solution[period][week] = [i + 1, j + 1]
    
    # Verifica che la soluzione sia completa
    for p in range(periods):
        for w in range(weeks):
            if solution[p][w] is None:
                print(f"Warning: Missing match for period {p}, week {w}")
                return None
    
    return solution


def extract_objective_value(model: Dict[str, Any], problem_type: str) -> Optional[int]:
    """
    Estrae il valore dell'obiettivo dal modello
    
    Args:
        model: Dizionario con le assegnazioni delle variabili
        problem_type: Tipo di problema
    
    Returns:
        Valore dell'obiettivo o None per problemi di decisione
    """
    
    if problem_type in ["decision1", "decision2", "decision3"]:
        return None  # Decision problems don't have objective values
    
    if problem_type == "optimization3":
        # Cerca max_abs_balance nel modello
        if "max_abs_balance" in model:
            return model["max_abs_balance"]
        
        # O cerca negli obiettivi
        if "objective" in model:
            return model["objective"]
    
    return None


def verify_solution_consistency(solution: List[List[List[int]]], n: int) -> Tuple[bool, str]:
    """
    Verifica la consistenza base di una soluzione
    
    Returns:
        (is_valid, error_message)
    """
    
    weeks = n - 1
    periods = n // 2
    
    if len(solution) != periods:
        return False, f"Wrong number of periods: {len(solution)} instead of {periods}"
    
    for p_idx, period in enumerate(solution):
        if len(period) != weeks:
            return False, f"Wrong number of weeks in period {p_idx}: {len(period)} instead of {weeks}"
        
        for w_idx, match in enumerate(period):
            if match is None:
                return False, f"Missing match at period {p_idx}, week {w_idx}"
            
            if len(match) != 2:
                return False, f"Invalid match format at period {p_idx}, week {w_idx}"
            
            t1, t2 = match
            if not (1 <= t1 <= n and 1 <= t2 <= n and t1 != t2):
                return False, f"Invalid teams in match at period {p_idx}, week {w_idx}: {match}"
    
    # Verifica che ogni squadra giochi una volta per settimana
    for w in range(weeks):
        teams_in_week = set()
        for p in range(periods):
            t1, t2 = solution[p][w]
            if t1 in teams_in_week or t2 in teams_in_week:
                return False, f"Team plays twice in week {w}"
            teams_in_week.add(t1)
            teams_in_week.add(t2)
        
        if len(teams_in_week) != n:
            return False, f"Not all teams play in week {w}"
    
    return True, "Solution is consistent"


def solution_to_dict(solution: List[List[List[int]]]) -> Dict:
    """
    Converte la soluzione in un dizionario serializzabile
    """
    if solution is None:
        return {}
    
    result = {}
    for p_idx, period in enumerate(solution):
        for w_idx, match in enumerate(period):
            if match:
                key = f"P{p_idx+1}_W{w_idx+1}"
                result[key] = match
    
    return result