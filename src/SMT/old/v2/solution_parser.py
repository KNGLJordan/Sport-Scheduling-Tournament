
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
