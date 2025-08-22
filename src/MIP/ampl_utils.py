
from amplpy import AMPL
import pandas as pd
import time
from solution_checker import check_solution

# ---------------------- UTILS -----------------------
def print_matrix(ampl,
                matrix_name: str, 
                row_range,
                col_range):
    """
    Prints a matrix from the AMPL model.
    Parameters:
        ampl (AMPL): An initialized AMPL object.
        matrix_name (str): The name of the matrix to be printed.
        row_range: Range of rows to print.
        col_range: Range of columns to print.
    Returns:
        None
    """
    m = ampl.get_variable(matrix_name).get_values()
        
    m_values =  m.to_pandas()[matrix_name+".val"]
        
    print(f"--------- {matrix_name.upper()} -----------")
    for i in row_range:
        for j in col_range:
            print(int(round(m_values[i][j])), end=" ")
        print()


def get_shark_solution(ampl,
                            n:int,
                            weeks_matrix_name: str,
                            periods_matrix_name: str,
                            home_matrix_name: str,
                            HM_mat_present: bool):
    """
    Returns the tournament solution based on the periods, weeks, and home matrices.
    Parameters:
        ampl (AMPL): An initialized AMPL object.
        n (int): The number of teams.
        weeks_matrix_name (str): The name of the weeks matrix.
        periods_matrix_name (str): The name of the periods matrix.
        home_matrix_name (str): The name of the home matrix.
        HM_mat_present (bool): Whether home matrix is present.
    Returns:
        solution (list): A list of lists representing the tournament solution.
    """
    solution = []

    periods = n//2
    weeks = n-1

    p = ampl.get_variable(periods_matrix_name).get_values()
    w = ampl.get_variable(weeks_matrix_name).get_values()

    if HM_mat_present:
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

    else:

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

def get_monkey_solution(ampl,
                            n: int,
                            matches_matrix_name: str,
                            periods_matrix_name: str,
                            home_matrix_name: str,
                            HM_mat_present: bool):
    """    Returns the tournament solution based on the matches, periods, and home matrices.
    Parameters:
        ampl (AMPL): An initialized AMPL object.
        n (int): The number of teams.
        matches_matrix_name (str): The name of the matches matrix.
        periods_matrix_name (str): The name of the periods matrix.
        home_matrix_name (str): The name of the home matrix.
        HM_mat_present (bool): Whether home matrix is present.
    Returns:
        solution (list): A list of lists representing the tournament solution.
    """
    solution = []

    weeks = n-1
    periods = n//2
    
    p = ampl.get_variable(periods_matrix_name).get_values()

    if HM_mat_present:
        h = ampl.get_variable(home_matrix_name).get_values()

        for pp in range(1, periods+1):
            period_solution = []
            for ww in range(1, weeks+1):
                match = [0, 0]
                for row_p, row_h in zip(p, h):

                    week = int(round(row_p[0]))
                    t = int(round(row_p[1]))
                    period = int(round(row_p[2]))
                    home = int(round(row_h[2]))
                    
                    if week == ww and period == pp and home == 1:
                        if match[0] == 0:
                            match[0] = t
                        else:
                            print(f"Error: more than one home team in week {ww} and period {pp}, found {match[0]} and {t}")
                    elif week == ww and period == pp and home == 0:
                        if match[1] == 0:
                            match[1] = t
                        else:
                            print(f"Error: more than one away team in week {ww} and period {pp}, found {match[1]} and {t}")
                    
                if match[0] == 0 or match[1] == 0:
                    print(f"Error: match not fully assigned in week {ww} and period {pp}")

                period_solution.append(match)

            solution.append(period_solution)

    else:
        for pp in range(1, periods+1):
            period_solution = []
            for ww in range(1, weeks+1):
                match = []  
                for row_p in p:

                    week = int(round(row_p[0]))
                    t = int(round(row_p[1]))
                    period = int(round(row_p[2]))
                    
                    if week == ww and period == pp:
                        match.append(t)
                
                if len(match) != 2:
                    print(f'Error: found {len(match)} teams in week {ww} and period {pp}, expected 2 teams.')

                period_solution.append(match)

            solution.append(period_solution)    

    return solution

def print_monkey(ampl,
                 n: int,
                 HM_mat_present: bool):
    
    # Print matches matrix
    print_matrix(ampl,
                    matrix_name='matches',
                    row_range=range(1, n),
                    col_range=range(1, n+1))
    
    # Print periods matrix
    print_matrix(ampl,
                    matrix_name='periods_matrix',
                    row_range=range(1, n),
                    col_range=range(1, n+1))
    
    if HM_mat_present:
        # Print home matrix
        print_matrix(ampl,
                    matrix_name='home_matrix',
                    row_range=range(1, n),
                    col_range=range(1, n+1))
    
def print_shark(ampl,
                 n: int,
                 HM_mat_present: bool):
    
    # print weeks_matrix
    print_matrix(ampl,
                matrix_name='weeks_matrix',
                row_range=range(1, n+1),
                col_range=range(1, n+1))

    # print periods_matrix
    print_matrix(ampl,
                matrix_name='periods_matrix',
                row_range=range(1, n+1),
                col_range=range(1, n+1))
    
    if HM_mat_present:
        # print home_matrix
        print_matrix(ampl,
                    matrix_name='home_matrix',
                    row_range=range(1, n+1),
                    col_range=range(1, n+1))

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
    # ampl.set_option("presolve", 10)
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
        ampl.solve(verbose=False)
    except KeyboardInterrupt:
        print("\n...interrupted!")
        return time_limit
    
    # Stop time
    elapsed = time.time() - start_time

    # Check if the solution is model is optimized
    optimization = False
    objective_val = None
    try:
        objective_val = round(ampl.get_objective(objective).value())
        optimization = True
    except Exception as e:
        optimization = False
        # print("\t\tNo optimization.")

    # Status
    if (ampl.solve_result != 'solved') or (optimization and (objective_val < 0)):
        print("\t\tSolution not found.")
        return elapsed, False, None, None

    HM_mat_present = True
    try:
        ampl.get_variable("home_matrix")
    except Exception as e:
        HM_mat_present = False
        

    # Get solution
    if "monkey" in model_filename:
        sol = get_monkey_solution(ampl=ampl,
                                  n=n,
                                  matches_matrix_name='matches',
                                  periods_matrix_name='periods_matrix',
                                  home_matrix_name='home_matrix',
                                  HM_mat_present=HM_mat_present)
    elif "shark" in model_filename:
        sol = get_shark_solution(ampl=ampl,
                                 n=n,
                                 weeks_matrix_name='weeks_matrix',
                                 periods_matrix_name='periods_matrix',
                                 home_matrix_name='home_matrix',
                                 HM_mat_present=HM_mat_present)
    else:
        print("\t\tUnknown model type. Cannot get solution.")
        sol = None
    
    if not all(sol): # redoundand check
        sol = None
        print("\t\tNo solution found or solution is empty.")
    else:
        print(f"\t\tSolution found in {elapsed:.1f}s.")

    # Print solution if required
    if sol and print_solution:

        if "monkey" in model_filename:

            print_monkey(ampl, 
                         n=n,
                         HM_mat_present=HM_mat_present)

        elif "shark" in model_filename:

            print_shark(ampl,
                        n=n,
                        HM_mat_present=HM_mat_present)
            
        else:

            print("Unknown model type. Cannot print solution.")
            
            
        print_tournament(sol)

    # optimal, a Boolean true iff the instance is solved for the decision version, or solved to optimality for the optimization version
    if (not optimization) or (optimization and elapsed < time_limit): # optimal 
        optimal = True
    else:
        optimal = False

    return elapsed, optimal, objective_val, sol
