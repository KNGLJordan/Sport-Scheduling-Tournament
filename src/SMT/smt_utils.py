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
    
    w_vals = {}  # W_i_j -> week
    p_vals = {}  # P_i_j -> period  
    h_vals = {}  # H_i_j -> bool (home)
    
    # Try different parsing patterns for different solver outputs
    
    # Pattern 1: Z3/CVC5 format with define-fun
    # (define-fun M_0_1 () Int 2)
    define_pattern = r'\(define-fun\s+(\w+)_(\d+)_(\d+)\s+\(\)\s+(\w+)\s+([^\)]+)\)'
    matches = re.findall(define_pattern, model_output)
    
    for match in matches:
        var_type, i, j, data_type, value = match
        i, j = int(i), int(j)
        
        if var_type == 'W':
            w_vals[(i, j)] = int(value)
        elif var_type == 'P':
            p_vals[(i, j)] = int(value)
        elif var_type == 'H':
            h_vals[(i, j)] = value.lower() == 'true'
    
    # Pattern 2: MathSAT format
    # ( (M_0_1 2) )
    mathsat_pattern = r'\(\s*\((\w+)_(\d+)_(\d+)\s+([^\)]+)\)\s*\)'
    if not w_vals:  # Only try if first pattern didn't work
        matches = re.findall(mathsat_pattern, model_output)
        for match in matches:
            var_type, i, j, value = match
            i, j = int(i), int(j)
            
            if var_type == 'W':
                w_vals[(i, j)] = int(value)
            elif var_type == 'P':
                p_vals[(i, j)] = int(value)
            elif var_type == 'H':
                h_vals[(i, j)] = value.lower() == 'true'
    
    # Pattern 3: Simple format
    # M_0_1 = 2
    simple_pattern = r'(\w+)_(\d+)_(\d+)\s*=\s*([^\s\)]+)'
    if not w_vals:  # Only try if previous patterns didn't work
        matches = re.findall(simple_pattern, model_output)
        for match in matches:
            var_type, i, j, value = match
            i, j = int(i), int(j)
            
            if var_type == 'W':
                w_vals[(i, j)] = int(value)
            elif var_type == 'P':
                p_vals[(i, j)] = int(value)
            elif var_type == 'H':
                h_vals[(i, j)] = value.lower() in ['true', '1']
    
    # Build solution from parsed values
    matches_found = False
    for i in range(n):
        for j in range(i + 1, n):
            if (i, j) in w_vals and (i, j) in p_vals:
                week = w_vals[(i, j)]
                period = p_vals[(i, j)]
                
                # Determine home team for optimization problem
                if h_vals and (i, j) in h_vals:
                    if h_vals[(i, j)]:
                        match = [i + 1, j + 1]  # i is home
                    else:
                        match = [j + 1, i + 1]  # j is home
                else:
                    # No home info (decision problem), just use natural order
                    match = [i + 1, j + 1]
                
                if 0 <= period < periods and 0 <= week < weeks:
                    solution[period][week] = match
                    matches_found = True
    
    if not matches_found:
        return None, None
    
    # Extract objective value for optimization
    obj = None
    if is_optimization:
        # Try different patterns for objective value
        obj_patterns = [
            r'\(define-fun\s+max_abs_balance\s+\(\)\s+Int\s+(\d+)\)',
            r'\(\s*\(max_abs_balance\s+(\d+)\)\s*\)',
            r'max_abs_balance\s*=\s*(\d+)',
            r'objectives:\s*\(max_abs_balance\s+(\d+)\)'
        ]
        
        for pattern in obj_patterns:
            obj_matches = re.findall(pattern, model_output)
            if obj_matches:
                obj = int(obj_matches[0])
                break
    
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