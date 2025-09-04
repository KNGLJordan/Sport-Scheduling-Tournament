"""
Runner per eseguire diversi solver SMT e catturare i risultati
"""

import subprocess
import tempfile
import os
import time
from typing import Tuple, Optional, Dict, Any
import re

class SMTSolver:
    """Classe base per i solver SMT"""
    
    def __init__(self, name: str, command: str):
        self.name = name
        self.command = command
    
    def run(self, smt_content: str, timeout: int = 300) -> Tuple[str, float, bool]:
        """
        Esegue il solver con il contenuto SMT-LIB
        Ritorna: (output, elapsed_time, timed_out)
        """
        with tempfile.NamedTemporaryFile(mode='w', suffix='.smt2', delete=False) as f:
            f.write(smt_content)
            temp_file = f.name
        
        try:
            start_time = time.time()
            cmd = self.command.format(file=temp_file)
            
            result = subprocess.run(
                cmd.split(),
                capture_output=True,
                text=True,
                timeout=timeout
            )
            
            elapsed = time.time() - start_time
            return result.stdout, elapsed, False
            
        except subprocess.TimeoutExpired:
            elapsed = time.time() - start_time
            return "", elapsed, True
            
        finally:
            if os.path.exists(temp_file):
                os.remove(temp_file)


class Z3Solver(SMTSolver):
    def __init__(self):
        super().__init__("z3", "z3 -smt2 {file}")
    
    def parse_model(self, output: str) -> Dict[str, Any]:
        """Parsa il modello dall'output di Z3"""
        model = {}
        
        # Cerca sat/unsat
        if "unsat" in output:
            return {"status": "unsat"}
        elif "sat" not in output:
            return {f"status": f"{output}]"}
        
        model["status"] = "sat"
        
        # Parsa le assegnazioni delle variabili
        # Z3 output format: (define-fun var_name () Type value)
        pattern = r'\(define-fun\s+(\w+)\s+\(\)\s+\w+\s+([^\)]+)\)'
        matches = re.findall(pattern, output)
        
        for var_name, value in matches:
            # Converti il valore nel tipo appropriato
            if value == "true":
                model[var_name] = True
            elif value == "false":
                model[var_name] = False
            else:
                try:
                    model[var_name] = int(value)
                except:
                    model[var_name] = value
        
        # Cerca obiettivi per problemi di ottimizzazione
        obj_pattern = r'\(objectives\s*\(([^\)]+)\)\s*\)'
        obj_match = re.search(obj_pattern, output)
        if obj_match:
            try:
                model["objective"] = int(obj_match.group(1))
            except:
                pass
        
        return model


class CVC5Solver(SMTSolver):
    def __init__(self):
        super().__init__("cvc5", "cvc5 --produce-models {file}")
    
    def parse_model(self, output: str) -> Dict[str, Any]:
        """Parsa il modello dall'output di CVC5"""
        model = {}
        
        if "unsat" in output:
            return {"status": "unsat"}
        elif "sat" not in output:
            return {"status": f"{output}"}
        
        model["status"] = "sat"
        
        # CVC5 output format simile a Z3
        pattern = r'\(define-fun\s+(\w+)\s+\(\)\s+\w+\s+([^\)]+)\)'
        matches = re.findall(pattern, output)
        
        for var_name, value in matches:
            if value == "true":
                model[var_name] = True
            elif value == "false":
                model[var_name] = False
            else:
                try:
                    model[var_name] = int(value)
                except:
                    model[var_name] = value
        
        return model


class MathSATSolver(SMTSolver):
    def __init__(self):
        super().__init__("mathsat", "mathsat -model {file}")
    
    def parse_model(self, output: str) -> Dict[str, Any]:
        """Parsa il modello dall'output di MathSAT"""
        model = {}
        
        if "unsat" in output:
            return {"status": "unsat"}
        elif "sat" not in output:
            return {"status": "unknown"}
        
        model["status"] = "sat"
        
        # MathSAT output format
        pattern = r'\(\s*=\s+(\w+)\s+([^\)]+)\)'
        matches = re.findall(pattern, output)
        
        for var_name, value in matches:
            if value == "true":
                model[var_name] = True
            elif value == "false":
                model[var_name] = False
            else:
                try:
                    model[var_name] = int(value)
                except:
                    model[var_name] = value
        
        return model


class Yices2Solver(SMTSolver):
    def __init__(self):
        super().__init__("yices2", "yices-smt2 --model {file}")
    
    def parse_model(self, output: str) -> Dict[str, Any]:
        """Parsa il modello dall'output di Yices2"""
        model = {}
        
        if "unsat" in output:
            return {"status": "unsat"}
        elif "sat" not in output:
            return {"status": f"{output}"}
        
        model["status"] = "sat"
        
        # Yices2 output format
        pattern = r'\(=\s+(\w+)\s+([^\)]+)\)'
        matches = re.findall(pattern, output)
        
        for var_name, value in matches:
            if value == "true":
                model[var_name] = True
            elif value == "false":
                model[var_name] = False
            else:
                try:
                    model[var_name] = int(value)
                except:
                    model[var_name] = value
        
        return model


# Registry dei solver disponibili
AVAILABLE_SOLVERS = {
    "z3": Z3Solver,
    "cvc5": CVC5Solver,
    "mathsat": MathSATSolver,
    "yices2": Yices2Solver,
}


def get_solver(solver_name: str) -> Optional[SMTSolver]:
    """Ottiene un'istanza del solver richiesto"""
    if solver_name in AVAILABLE_SOLVERS:
        return AVAILABLE_SOLVERS[solver_name]()
    return None
