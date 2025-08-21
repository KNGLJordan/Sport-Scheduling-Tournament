include "globals.mzn";

% --- PARAMETERS ---

int: n; % number of teams
int: weeks = n-1; % number of weeks
int: periods = n div 2; % number of periods

% --- VARIABLES ---

array[1..weeks, 1..n] of var 1..n: matches; % for every team and week, the opponent
array[1..weeks, 1..n] of var 1..periods: periods_matrix;  % for every team and week, the period of the match

% --- CONSTRAINTS ---

% 1. every team plays with every other team only once
constraint
  forall(t in 1..n)(alldifferent([t] ++ [matches[w, t] | w in 1..weeks]))::domain_propagation;
  
% 2. every team plays once a week
constraint
  forall(w in 1..weeks)(alldifferent([matches[w, t] | t in 1..n]));
  
% 3. every team plays at most twice in the same period over the tournament  
constraint 
  forall(t in 1..n, p in 1..periods)(count([periods_matrix[w, t] | w in 1..weeks], p) < 3)::domain_propagation;
  
% 4. every period have exactly two teams per week
constraint
  forall(w in 1..weeks, p in 1..periods)(count([periods_matrix[w, t] | t in 1..n], p) = 2)::domain_propagation;
  
% 5. both team of a match have the same period
constraint
  forall(w in 1..weeks, t in 1..n)(periods_matrix[w, t] = periods_matrix[w, matches[w, t]])::domain_propagation;

% --- SOLVE ---

solve satisfy;