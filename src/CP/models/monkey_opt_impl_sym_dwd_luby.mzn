include "globals.mzn";

% --- PARAMETERS ---

int: n; % number of teams
int: weeks = n-1; % number of weeks
int: periods = n div 2; % number of periods

% --- SEARCH STRATEGY PARAMETERS ---

int: luby_value;


% --- VARIABLES ---

array[1..weeks, 1..n] of var 1..n: matches; % for every team and week, the opponent
array[1..weeks, 1..n] of var 1..periods: periods_matrix;  % for every team and week, the period of the match
array[1..weeks, 1..n] of var {0,1}: home_matrix;  % for every team and week, 1 if plays home, 0 if plays away

% --- OBJECTIVE ---

array[1..n] of var int: home_balance;

constraint
  forall(t in 1..n)(
    home_balance[t] = 2 * sum(w in 1..weeks)(home_matrix[w,t]) - weeks
  );

var int: unbalance_score = max(home_balance) - min(home_balance) - 2;

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

% 6. teams in a match plays home xor away
constraint
  forall(w in 1..weeks, t in 1..n)(home_matrix[w, t] != home_matrix[w, matches[w, t]])::domain_propagation;

% --- IMPLIED CONSTRAINTS ---

% 1. every match is symmetric
constraint
  forall(w in 1..weeks, t in 1..n)(matches[w, matches[w, t]] = t);

% --- SYMMETRY BREAKING ---

% 1. impose the columns of the matrix matches to be in lex order
constraint
  forall(w in 1..weeks-1, w2 in w+1..weeks)(lex_lesseq([matches[w,t] | t in 1..n], [matches[w2,t] | t in 1..n]));

% 2. same as above for periods
constraint
  forall(w in 1..weeks-1, w2 in w+1..weeks)(lex_lesseq([periods_matrix[w,t] | t in 1..n], [periods_matrix[w2,t] | t in 1..n]));  

% --- SOLVE ---

solve 
::int_search(matches, dom_w_deg, indomain_random)
::restart_luby(luby_value)
minimize abs(unbalance_score);