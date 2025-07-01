
from amplpy import AMPL
import pandas as pd
import time
from solution_checker import check_solution

# ---------------------- UTILS -----------------------
def print_square_matrix(ampl,
                       matrix_name: str, 
                       start_index: int,
                       end_index: int):
    """
    Prints a square matrix from the AMPL model.
    Parameters:
        ampl (AMPL): An initialized AMPL object.
        matrix_name (str): The name of the matrix to be printed.
        start_index (int): The starting index for the matrix.
        end_index (int): The ending index for the matrix.
    Returns:
        None
    """
    m = ampl.get_variable(matrix_name).get_values()
        
    m_values =  m.to_pandas()[matrix_name+".val"]
        
    print(f"--------- {matrix_name.upper()} -----------")
    for i in range(start_index,end_index+1):
        for j in range(start_index, end_index+1):
            print(int(round(m_values[i][j])), end=" ")
        print()

def get_solution_noHAmat(ampl,
                     n:int,
                     periods_matrix_name: str,
                     weeks_matrix_name: str):
    """
    Returns the tournament solution based on the periods and weeks matrices.
    Parameters:
        ampl (AMPL): An initialized AMPL object.
        n (int): The number of teams.
        periods_matrix_name (str): The name of the periods matrix.
        weeks_matrix_name (str): The name of the weeks matrix.
    Returns:
        solution (list): A list of lists representing the tournament solution.
    """

    solution = []
    
    periods = n//2
    weeks = n-1

    p = ampl.get_variable(periods_matrix_name).get_values()
    w = ampl.get_variable(weeks_matrix_name).get_values()

    for pp in range(1,periods+1):
        period_solution = []
        for ww in range(1,weeks+1):
            for row_p, row_w in zip(p, w):
                i = int(round(row_p[0]))    # keys.0
                j = int(round(row_p[1]))    # keys.1
                period = int(round(row_p[2]))  # value
                week = int(round(row_w[2]))    # value
                
                if i < j and pp==period and ww==week:
                    
                    period_solution.append([i,j])
        solution.append(period_solution)
    
    return solution
    

def get_solution(ampl,
                               n:int,
                               periods_matrix_name: str,
                               weeks_matrix_name: str,
                               home_matrix_name: str):
    """
    Returns the optimized tournament solution based on the periods, weeks, and home matrices.
    Parameters:
        ampl (AMPL): An initialized AMPL object.
        n (int): The number of teams.
        periods_matrix_name (str): The name of the periods matrix.
        weeks_matrix_name (str): The name of the weeks matrix.
        home_matrix_name (str): The name of the home matrix.
    Returns:
        solution (list): A list of lists representing the tournament solution.
    """
    solution = []

    periods = n//2
    weeks = n-1

    p = ampl.get_variable(periods_matrix_name).get_values()
    w = ampl.get_variable(weeks_matrix_name).get_values()
    h = ampl.get_variable(home_matrix_name).get_values()

    for pp in range(1,periods+1):
        period_solution = []
        for ww in range(1,weeks+1):
            for row_p, row_w, row_h in zip(p, w, h):

                i = int(round(row_p[0]))    # keys.0
                j = int(round(row_p[1]))    # keys.1
                period = int(round(row_p[2]))  # value
                week = int(round(row_w[2]))    # value
                i_at_home = int(round(row_h[2]))  # value  
                
                if i < j and pp==period and ww==week:

                    if i_at_home == 1: # i is at home
                        period_solution.append([i,j])
                    else: # j is at home
                        period_solution.append([j,i])
        
        solution.append(period_solution)
    
    return solution
    
def print_tournament(sol: list):
    """
    Prints the tournament solution in a readable format.
    Parameters:
        sol (list): A list of lists representing the tournament solution.
    Returns:
        None
    """
    periods = len(sol)
    weeks = periods * 2 - 1
    table = pd.DataFrame("", index=range(1, periods+1), columns=range(1, weeks+1))

    for pp in range(periods):
        for ww in range(weeks):
            table.at[pp+1, ww+1] = f"{sol[pp][ww]}"
    
    print("--------- TOURNAMENT -----------")
    print(table)

# ---------------------- FUNCTION FOR SOLVING AN INSTANCE OF THE PROBLEM -----------------------

def solve_mip(ampl: AMPL, 
              model_filename: str, 
              solver: str, 
              n: int,
              option_key: str = "",
              option_value: str = "",
              time_limit: int = 300,
              objective: str = "Unbalance",
              print_solution: bool = False):
    """
    Solves a MIP (Mixed Integer Programming) problem using the specified solver and model.

    Parameters:
        ampl (AMPL): An initialized AMPL object.
        model_filename (str): The filename of the AMPL model (.mod) to be loaded.
        solver (str): The solver to be used (e.g., 'gurobi', 'cbc', 'cplex').
        n (int): The value for the model parameter 'n'.
        option_key (str): Optional key to set a solver-specific option (e.g., 'gurobi_options').
        option_value (str): The corresponding value for the solver option (e.g., 'timelimit=300').
        time_limit (int): Maximum time (in seconds) allowed for solving the problem.
        print_solution (bool): Whether to print the resulting matrices and tournament table if solved within the time limit.

    Returns:
        float: The elapsed time (in seconds) used to solve the problem.
    """

    # Reset AMPL environment
    ampl.reset()

    # Set silent options
    ampl.set_option("log_file", "")       
    ampl.set_option("display_options", 0) 
    ampl.set_option("presolve", 0)
    ampl.set_option("solver_msg", 0) 
    ampl.set_option("solver", solver)

    # Check for an option to be set (the time limit)
    if option_value != "":
        ampl.set_option(option_key, option_value)

    # Read the model
    ampl.read(model_filename)

    # Set n
    ampl.param['n'] = n

    # Start time
    start_time = time.time()

    # Solve
    try:
        ampl.solve()
    except KeyboardInterrupt:
        print("\n...interrupted!")
        return time_limit
    
    # Stop time
    elapsed = time.time() - start_time

    # Print time
    print(f"n = {n}: {elapsed:.3f} sec.")

    # Check if the solution is model is optimized
    optimization = False
    objective_val = None
    try:
        objective_val = ampl.get_objective(objective).value()
        print(f"{objective}: {objective_val}")
        optimization = True
    except Exception as e:
        print("No optimization.")


    HM_mat_present = True
    try:
        ampl.get_variable("home_matrix")
    except Exception as e:
        HM_mat_present = False
        

    # Get solution
    if elapsed >= time_limit:
        sol = None
    elif HM_mat_present:
        sol = get_solution(ampl=ampl,
                            n=n,
                            periods_matrix_name='periods_matrix',
                            weeks_matrix_name='weeks_matrix',
                            home_matrix_name='home_matrix')
    else:
        sol = get_solution_noHAmat(ampl=ampl,
                            n=n,
                            periods_matrix_name='periods_matrix',
                            weeks_matrix_name='weeks_matrix')
    

    # Check solution
    if sol:
        print(check_solution(sol))

    # Print solution if required
    if sol and print_solution and elapsed < time_limit:

        # Stampa periods_matrix
        print_square_matrix(ampl,
                            matrix_name='periods_matrix',
                            start_index=1,
                            end_index=n)

        # Stampa weeks_matrix
        print_square_matrix(ampl,
                            matrix_name='weeks_matrix',
                            start_index=1,
                            end_index=n)

        if optimization:

            print_square_matrix(ampl,
                                matrix_name='home_matrix',
                                start_index=1,
                                end_index=n)
            
            
        print_tournament(sol)

    return elapsed, optimization, objective_val, sol