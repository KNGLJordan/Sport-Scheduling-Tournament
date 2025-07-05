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
  forall(t in 1..n)(alldifferent([t] ++ [matches[w, t] | w in 1..weeks]));
  
% 2. every team plays once a week
constraint
  forall(w in 1..weeks)(alldifferent([matches[w, t] | t in 1..n]));
  
% % every match is symmetric (implicit?)
% constraint
%   forall(w in 1..weeks, t in 1..n)(matches[w, matches[w, t]] = t);
  
% 3. every team plays at most twice in the same period over the tournament  
constraint 
  forall(t in 1..n, p in 1..periods)(count([periods_matrix[w, t] | w in 1..weeks], p) < 3);

% 4. both team of a match have the same period
constraint
  forall(w in 1..weeks, t in 1..n)(periods_matrix[w, t] = periods_matrix[w, matches[w, t]]);

% 5. every period have exactly two teams per week
constraint
  forall(w in 1..weeks, p in 1..periods)(count([periods_matrix[w, t] | t in 1..n], p) = 2);
  
% --- SYMMETRY BREAKING ---

% 6. impose the columns of the matrix matches to be in lex order
constraint
  forall(w in 1..weeks-1, w2 in w+1..weeks)(lex_lesseq([matches[w,t] | t in 1..n], [matches[w2,t] | t in 1..n]));

% 7. same as above for periods
constraint
  forall(w in 1..weeks-1, w2 in w+1..weeks)(lex_lesseq([periods_matrix[w,t] | t in 1..n], [periods_matrix[w2,t] | t in 1..n]));  

% --- SOLVE ---

solve satisfy;

  