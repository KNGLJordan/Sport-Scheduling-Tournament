include "alldifferent.mzn";
include "globals.mzn";

int: n; % number of teams
int: weeks = n-1; % number of weeks
int: periods = n div 2; % number of periods

array[1..n, 1..n] of var 0..n-1: weeks_matrix; % for every pair of team the week they play against each other
array[1..n, 1..n] of var 0..periods: periods_matrix;  % for every pair of team the period they play against each other


% every team plays with every other team only once 
% every team plays once a week
constraint
  forall(t1 in 1..n)(alldifferent([weeks_matrix[t1, t2] | t2 in 1..n]))::domain_propagation;
constraint
  forall(t1 in 1..n)(alldifferent([weeks_matrix[t2, t1] | t2 in 1..n]))::domain_propagation;
constraint
  forall(t in 1..n)(weeks_matrix[t,t] = 0)::domain_propagation;
constraint
  forall(t1 in 1..n-1, t2 in t1+1..n)(weeks_matrix[t1,t2] = weeks_matrix[t2,t1])::domain_propagation;
  
% every team plays at most twice in the same period over the tournament  
constraint 
  forall(t1 in 1..n, p in 1..periods)(count([periods_matrix[t1, t2] | t2 in 1..n], p) < 3)::domain_propagation;
constraint 
  forall(t1 in 1..n, p in 1..periods)(count([periods_matrix[t2, t1] | t2 in 1..n], p) < 3)::domain_propagation;
constraint
  forall(t in 1..n)(periods_matrix[t,t] = 0)::domain_propagation;
constraint
  forall(t1 in 1..n, t2 in 1..n where t1 != t2)(periods_matrix[t1,t2] != 0)::domain_propagation;
constraint
  forall(t1 in 1..n-1, t2 in t1+1..n)(periods_matrix[t1,t2] = periods_matrix[t2,t1])::domain_propagation;
  
%channeling (only for printing...)
array[1..weeks, 1..periods, 1..2] of var 0..n: tournament;

constraint
  forall(i, j in 1..n where i < j) (
    let {
      var 0..weeks: w = weeks_matrix[i,j],
      var 0..periods: p = periods_matrix[i,j]
    } in
      tournament[w, p, 1] = i /\
      tournament[w, p, 2] = j
  )::domain_propagation;

  
% symmetry beaking constraint: we impose the columns of the matrix weeks to be in lex order
constraint
  forall(t1 in 1..n-1, t2 in t1+1..n)(lex_lesseq([weeks_matrix[t1,t] | t in 1..n], [weeks_matrix[t2,t] | t in 1..n]));
  
 % symmetry beaking constraint: we impose the columns of the matrix periods to be in lex order
constraint
  forall(t1 in 1..n-1, t2 in t1+1..n)(lex_lesseq([periods_matrix[t1,t] | t in 1..n], [periods_matrix[t2,t] | t in 1..n]));
  
  
solve satisfy;

output [
  "              " ++
  concat([ "Week " ++ show(w) ++ "        " | w in 1..weeks ]) ++ "\n" ++
  "           " ++ concat([ "--------------" | w in 1..weeks ]) ++ "\n" ++
  concat([
    "Period " ++ show(p) ++ ": |   " ++
    concat([
      concat([
        if fix(periods_matrix[t1,t2]) = p /\ fix(weeks_matrix[t1,t2]) = w then
          " " ++ show(t1) ++ " v " ++ show(t2) ++ "    |   "
        else
          ""
        endif
        | t1 in 1..n, t2 in 1..n where t1<t2
      ])
      | w in 1..weeks
    ]) ++ "\n" ++
    "           " ++ concat([ "--------------" | w in 1..weeks ]) ++ "\n"
    | p in 1..periods
  ])
];
