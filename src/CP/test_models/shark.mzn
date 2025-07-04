include "globals.mzn";

% --- PARAMETERS ---

int: n; % number of teams
int: weeks = n-1; % number of weeks
int: periods = n div 2; % number of periods

% --- VARIABLES ---

array[1..n, 1..n] of var 0..n-1: weeks_matrix; % for every pair of team the week they play against each other
array[1..n, 1..n] of var 0..periods: periods_matrix;  % for every pair of team the period they play against each other

% --- CONSTRAINTS ---

  % --- WEEK MATRIX ---

% 1. every team plays with every other team only once and plays once a week
constraint
  forall(t1 in 1..n)(alldifferent([weeks_matrix[t1, t2] | t2 in 1..n]));

% this constraint became useless since is it imposed the symmetry w.r.t. the diagonal
% constraint
%   forall(t1 in 1..n)(alldifferent([weeks_matrix[t2, t1] | t2 in 1..n]))::domain_propagation;
  
% 2. every team does not play against himself
constraint
  forall(t in 1..n)(weeks_matrix[t,t] = 0);
  
% 3. the matches are symmetric (if 1 plays against 2 on week 1, then also 2 plays against 1 on week 1)
constraint
  forall(t1 in 1..n-1, t2 in t1+1..n)(weeks_matrix[t1,t2] = weeks_matrix[t2,t1]);

  % --- PERIOD MATRIX ---

% 4. every team plays at most twice in the same period over the tournament  
constraint 
  forall(t1 in 1..n, p in 1..periods)(count([periods_matrix[t1, t2] | t2 in 1..n], p) < 3);

% this constraint became useless since is it imposed the symmetry w.r.t. the diagonal
% constraint 
%   forall(t1 in 1..n, p in 1..periods)(count([periods_matrix[t2, t1] | t2 in 1..n], p) < 3)::domain_propagation;

% 5. every team does not play against himself
constraint
  forall(t in 1..n)(periods_matrix[t,t] = 0);
  
% 6. every match is on a valid period
constraint
  forall(t1 in 1..n, t2 in 1..n where t1 != t2)(periods_matrix[t1,t2] != 0);
  
% 7. every period have the same number of matches
constraint
  forall(p in 1..periods)(count([periods_matrix[t1, t2] | t1 in 1..n, t2 in 1..n], p) = ((n*weeks)/periods));

% 8. the periods are symmetric (if 1 plays agains 2 on period 1, then also 2 plays against 1 on period 1)
constraint
  forall(t1 in 1..n-1, t2 in t1+1..n)(periods_matrix[t1,t2] = periods_matrix[t2,t1]);
  
% 9. all the matches played in the same week have to be in different periods
constraint
  forall(w in 1..weeks)(alldifferent([periods_matrix[t1, t2] | t1 in 1..n-1, t2 in t1..n where weeks_matrix[t1, t2] = w]));

% --- SOLVE ---
  
solve satisfy;

