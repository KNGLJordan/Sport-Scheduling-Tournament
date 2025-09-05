import subprocess
import tempfile
import os
import re

def run_smt_solver(smtlib_content: str,
                   solver_config: dict,
                   timeout: int,
                   seed: int,
                   is_optimization: bool = False):

    # Create temp file for SMT-lib content
    with tempfile.NamedTemporaryFile(mode='w', suffix='.smt2', delete=False) as f:
        temp_file = f.name
        f.write(smtlib_content)
    
    try:
        solver_name = solver_config['command']
        cmd = [solver_name]
        
        # solvers options
        if 'z3' in solver_name:
            cmd.append(f"{solver_config['timeout_flag']}{timeout}")
            cmd.append(f"{solver_config['seed_flag']}{seed}")
            if is_optimization:
                pass
        
        elif 'cvc5' in solver_name:
            cmd.append(f"{solver_config['timeout_flag']}{timeout}000")
            cmd.append(solver_config['model_flag'])
            if not is_optimization:
                cmd.append('--incremental')
                cmd.append('--produce-models')
            cmd.append(f"{solver_config['seed_flag']}{seed}")
        
        elif 'mathsat' in solver_name:
            cmd.append(f"{solver_config['timeout_flag']}{timeout}")
            cmd.append(f"{solver_config['seed_flag']}{seed}")
            cmd.append('-model')
            if is_optimization:
                cmd.append('-opt.priority=box')
        
        elif 'yices' in solver_name:
            cmd.append(f"{solver_config['timeout_flag']}{timeout}")
            cmd.append('--incremental')
        
        cmd.append(temp_file)
        
        try:
            result = subprocess.run(
                cmd,
                capture_output=True,
                text=True,
                timeout=timeout
            )
            output = result.stdout
            error = result.stderr
            
            if not output and error:
                print(f"\t\tSolver stderr: {error[:200]}")
            
            if 'z3' in solver_name:
                if 'sat' in output and 'unsat' not in output:
                    return 'sat', output
                elif 'unsat' in output:
                    return 'unsat', None
                else:
                    return 'unknown', None
            
            elif 'cvc5' in solver_name:
                if 'sat' in output and 'unsat' not in output:
                    return 'sat', output
                elif 'unsat' in output:
                    return 'unsat', None
                else:
                    return 'unknown', None
            
            elif 'mathsat' in solver_name:
                if 'sat' in output:
                    if 'unsat' not in output:
                        return 'sat', output
                    else:
                        return 'unsat', None
                else:
                    return 'unknown', None
            
            elif 'yices' in solver_name:
                if 'sat' in output and 'unsat' not in output:
                    return 'sat', output
                elif 'unsat' in output:
                    return 'unsat', None
                else:
                    return 'unknown', None
            
            else:
                # generic
                if 'sat' in output and 'unsat' not in output:
                    return 'sat', output
                elif 'unsat' in output:
                    return 'unsat', None
                else:
                    return 'unknown', None
                
        except subprocess.TimeoutExpired:
            return 'timeout', None
            
    finally:
        # Clean up temp file
        if os.path.exists(temp_file):
            os.unlink(temp_file)

def parse_solution(model_output: str, n: int, is_optimization: bool = False):
    if not model_output:
        return None, None
    
    weeks = n - 1
    periods = n // 2
    solution = [[None for _ in range(weeks)] for _ in range(periods)]
    
    w_vals = {}
    p_vals = {}
    h_vals = {}
    
    # Yices2 format: (= W_0_1 4)
    if "(= W_" in model_output:
        matches = re.findall(r'\(=\s+(\w+)_(\d+)_(\d+)\s+(\d+)\)', model_output)
        for var_type, i, j, value in matches:
            i, j = int(i), int(j)
            if var_type == 'W':
                w_vals[(i, j)] = int(value)
            elif var_type == 'P':
                p_vals[(i, j)] = int(value)
            elif var_type == 'H':
                h_vals[(i, j)] = int(value) == 1
    
    # MathSAT/Z3/CVC5 format: (define-fun W_0_1 () Int 0)
    elif "define-fun" in model_output:
        matches = re.findall(r'\(define-fun\s+(\w+)_(\d+)_(\d+)\s+\(\)\s+\w+\s+([^\)]+)\)', model_output)
        for var_type, i, j, value in matches:
            i, j = int(i), int(j)
            if var_type == 'W':
                w_vals[(i, j)] = int(value)
            elif var_type == 'P':
                p_vals[(i, j)] = int(value)
            elif var_type == 'H':
                h_vals[(i, j)] = value.strip().lower() == 'true'
    
    for i in range(n):
        for j in range(i + 1, n):
            if (i, j) in w_vals and (i, j) in p_vals:
                week = w_vals[(i, j)]
                period = p_vals[(i, j)]
                
                if h_vals and (i, j) in h_vals:
                    match = [i + 1, j + 1] if h_vals[(i, j)] else [j + 1, i + 1]
                else:
                    match = [i + 1, j + 1]
                
                if 0 <= period < periods and 0 <= week < weeks:
                    solution[period][week] = match
    
    # Get objective for optimization
    obj = None
    if is_optimization:
        obj_match = re.search(r'(?:define-fun|=)\s+(?:max_abs_balance|obj)\s+(?:\(\)\s+Int\s+)?(\d+)', model_output)
        if obj_match:
            obj = int(obj_match.group(1))
    
    return solution, obj

def validate_solution_structure(solution: list, n: int):
    """
    Basic validation of solution structure
    """
    if not solution:
        return False
    
    weeks = n - 1
    periods = n // 2
    
    if len(solution) != periods:
        return False
    
    for period in solution:
        if len(period) != weeks:
            return False
    
    return True