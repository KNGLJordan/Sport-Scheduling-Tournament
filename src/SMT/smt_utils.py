import subprocess
import tempfile
import os
import re

def run_smt_solver(smtlib_content: str,
                   solver_config: dict,
                   timeout: int,
                   seed: int,
                   is_optimization: bool = False):
    """
    Execute SMT solver with given SMT-lib content
    Returns: (result_status, model_output)
    """
    
    # Create temp file for SMT-lib content
    with tempfile.NamedTemporaryFile(mode='w', suffix='.smt2', delete=False) as f:
        temp_file = f.name
        f.write(smtlib_content)
    
    try:
        # Build command based on solver
        solver_name = solver_config['command']
        cmd = [solver_name]
        
        # Configure solver-specific options
        if 'z3' in solver_name:
            # Z3 configuration
            cmd.append(f"{solver_config['timeout_flag']}{timeout}")
            cmd.append(f"{solver_config['seed_flag']}{seed}")
            if is_optimization:
                # Z3 handles optimization natively
                pass
        
        elif 'cvc5' in solver_name:
            # CVC5 configuration
            cmd.append(f"{solver_config['timeout_flag']}{timeout}000")  # ms
            cmd.append(solver_config['model_flag'])
            if not is_optimization:  # CVC5 doesn't support optimization well
                cmd.append('--incremental')
                cmd.append('--produce-models')
            cmd.append(f"{solver_config['seed_flag']}{seed}")
        
        elif 'mathsat' in solver_name:
            # MathSAT configuration
            cmd.append(f"{solver_config['timeout_flag']}{timeout}")
            cmd.append(f"{solver_config['seed_flag']}{seed}")
            cmd.append('-model')
            if is_optimization:
                cmd.append('-opt.priority=box')
        
        elif 'yices' in solver_name:
            # Yices2 configuration
            cmd.append(f"{solver_config['timeout_flag']}{timeout}")
            # Yices2 doesn't support random seed
            cmd.append('--incremental')
        
        # Add the SMT file
        cmd.append(temp_file)
        
        # Run solver
        try:
            result = subprocess.run(
                cmd,
                capture_output=True,
                text=True,
                timeout=timeout
            )
            output = result.stdout
            error = result.stderr
            
            # Debug output for troubleshooting
            if not output and error:
                print(f"\t\tSolver stderr: {error[:200]}")
            
            # Parse result based on solver
            if 'z3' in solver_name:
                if 'sat' in output and 'unsat' not in output:
                    return 'sat', output
                elif 'unsat' in output:
                    return 'unsat', None
                else:
                    return 'unknown', None
            
            elif 'cvc5' in solver_name:
                # CVC5 output format
                if 'sat' in output and 'unsat' not in output:
                    return 'sat', output
                elif 'unsat' in output:
                    return 'unsat', None
                else:
                    # CVC5 might need different parsing
                    return 'unknown', None
            
            elif 'mathsat' in solver_name:
                # MathSAT output format
                if 'sat' in output:
                    if 'unsat' not in output:
                        return 'sat', output
                    else:
                        return 'unsat', None
                else:
                    return 'unknown', None
            
            elif 'yices' in solver_name:
                # Yices output format
                if 'sat' in output and 'unsat' not in output:
                    return 'sat', output
                elif 'unsat' in output:
                    return 'unsat', None
                else:
                    return 'unknown', None
            
            else:
                # Generic parsing
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
    """
    Parse SMT solver output to extract solution
    Returns: (solution, objective_value)
    """
    
    if not model_output:
        return None, None
    
    weeks = n - 1
    periods = n // 2
    
    # Initialize solution structure
    solution = [[None for _ in range(weeks)] for _ in range(periods)]
    
    # Store parsed values
    m_vals = {}  # M_i_j -> week
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
        
        if var_type == 'M':
            m_vals[(i, j)] = int(value)
        elif var_type == 'P':
            p_vals[(i, j)] = int(value)
        elif var_type == 'H':
            h_vals[(i, j)] = value.lower() == 'true'
    
    # Pattern 2: MathSAT format
    # ( (M_0_1 2) )
    mathsat_pattern = r'\(\s*\((\w+)_(\d+)_(\d+)\s+([^\)]+)\)\s*\)'
    if not m_vals:  # Only try if first pattern didn't work
        matches = re.findall(mathsat_pattern, model_output)
        for match in matches:
            var_type, i, j, value = match
            i, j = int(i), int(j)
            
            if var_type == 'M':
                m_vals[(i, j)] = int(value)
            elif var_type == 'P':
                p_vals[(i, j)] = int(value)
            elif var_type == 'H':
                h_vals[(i, j)] = value.lower() == 'true'
    
    # Pattern 3: Simple format
    # M_0_1 = 2
    simple_pattern = r'(\w+)_(\d+)_(\d+)\s*=\s*([^\s\)]+)'
    if not m_vals:  # Only try if previous patterns didn't work
        matches = re.findall(simple_pattern, model_output)
        for match in matches:
            var_type, i, j, value = match
            i, j = int(i), int(j)
            
            if var_type == 'M':
                m_vals[(i, j)] = int(value)
            elif var_type == 'P':
                p_vals[(i, j)] = int(value)
            elif var_type == 'H':
                h_vals[(i, j)] = value.lower() in ['true', '1']
    
    # Build solution from parsed values
    matches_found = False
    for i in range(n):
        for j in range(i + 1, n):
            if (i, j) in m_vals and (i, j) in p_vals:
                week = m_vals[(i, j)]
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