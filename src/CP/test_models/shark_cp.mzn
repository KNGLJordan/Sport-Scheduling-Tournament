% CHUFFED 0.13.2
% n = 12: 3s 683msec.
% n = 14: 2m 49s.
% n = 16: Time limit

include "globals.mzn";

int: n; % number of teams
int: weeks = n-1; % number of weeks
int: periods = n div 2; % number of periods

array[1..n, 1..n] of var 0..n-1: weeks_matrix; % for every pair of team the week they play against each other
array[1..n, 1..n] of var 0..periods: periods_matrix;  % for every pair of team the period they play against each other


% WEEK MATRIX
% every team plays with every other team only once and plays once a week
constraint
  forall(t1 in 1..n)(alldifferent([weeks_matrix[t1, t2] | t2 in 1..n]));

% this constraint became useless since is it imposed the symmetry w.r.t. the diagonal
% constraint
%   forall(t1 in 1..n)(alldifferent([weeks_matrix[t2, t1] | t2 in 1..n]))::domain_propagation;
  
% every team does not play against himself
constraint
  forall(t in 1..n)(weeks_matrix[t,t] = 0);
  
% the matches are symmetric (if 1 plays against 2 on week 1, then also 2 plays against 1 on week 1)
constraint
  forall(t1 in 1..n-1, t2 in t1+1..n)(weeks_matrix[t1,t2] = weeks_matrix[t2,t1]);

% PERIOD MATRIX
% every team plays at most twice in the same period over the tournament  
constraint 
  forall(t1 in 1..n, p in 1..periods)(count([periods_matrix[t1, t2] | t2 in 1..n], p) < 3);

% this constraint became useless since is it imposed the symmetry w.r.t. the diagonal
% constraint 
%   forall(t1 in 1..n, p in 1..periods)(count([periods_matrix[t2, t1] | t2 in 1..n], p) < 3)::domain_propagation;

% every team does not play against himself
constraint
  forall(t in 1..n)(periods_matrix[t,t] = 0);
  
% every match is on a valid period
constraint
  forall(t1 in 1..n, t2 in 1..n where t1 != t2)(periods_matrix[t1,t2] != 0);
  
% every period have the same number of matches
constraint
  forall(p in 1..periods)(count([periods_matrix[t1, t2] | t1 in 1..n, t2 in 1..n], p) = ((n*weeks)/periods));

% the periods are symmetric (if 1 plays agains 2 on period 1, then also 2 plays against 1 on period 1)
constraint
  forall(t1 in 1..n-1, t2 in t1+1..n)(periods_matrix[t1,t2] = periods_matrix[t2,t1]);
  
% all the matches played in the same week have to be in different periods
constraint
  forall(w in 1..weeks)(alldifferent([periods_matrix[t1, t2] | t1 in 1..n-1, t2 in t1..n where weeks_matrix[t1, t2] = w]));


% SYMMETRY BREAKING
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

%   % ----------- For Debug ----------- %
%   ++
%   % ----------- Weeks matrix (n x n) ----------- %
%   "\n\nWeeks Matrix:\n" ++
%   concat([ concat([ show(fix(weeks_matrix[i,j])) ++ " " | j in 1..n ]) ++ "\n" | i in 1..n ]) ++

%   % ----------- Periods matrix (n x n) ----------- %
%   "\nPeriods Matrix:\n" ++
%   concat([ concat([ show(fix(periods_matrix[i,j])) ++ " " | j in 1..n ]) ++ "\n" | i in 1..n ]) 
];
