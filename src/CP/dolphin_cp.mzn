include "alldifferent.mzn";
include "globals.mzn";

int: n; % number of teams
int: weeks = n-1; % number of weeks
int: periods = n div 2; % number of periods

array[1..weeks, 1..n] of var 1..n: matches; % for every team and week, the opponent
array[1..weeks, 1..n] of var 1..n: periods_matrix;  % for every team and week, the period of the match


% every team plays with every other team only once
constraint
  forall(t in 1..n)(alldifferent([t] ++ [matches[w, t] | w in 1..weeks]))::domain_propagation;
  
% every team plays once a week
constraint
  forall(w in 1..weeks)(alldifferent([matches[w, t] | t in 1..n]))::domain_propagation;
  
% every team plays at most twice in the same period over the tournament  
constraint 
  forall(t in 1..n)(alldifferent([periods_matrix[w, t] | w in 1..weeks]))::domain_propagation;

% both team of a match have the same period
constraint
  forall(w in 1..weeks, t in 1..n)
  (periods_matrix[w, t] mod periods = periods_matrix[w, matches[w, t]] mod periods)::domain_propagation;

% every period have exactly two teams per week
constraint
  forall(w in 1..weeks)(alldifferent([periods_matrix[w, t] | t in 1..n]))::domain_propagation;
  
% symmetry beaking constraint: we impose the columns of the matrix matches to be in lex order
% constraint
%   forall(w in 1..weeks-1, w2 in w+1..weeks)
%   (lex_lesseq([matches[w,t] | t in 1..n], [matches[w2,t] | t in 1..n]))::domain_propagation;

% symmetry breaking for periods
% constraint
%   forall(w in 1..weeks-1, w2 in w+1..weeks)
%   (lex_lesseq([periods_matrix[w,t] | t in 1..n], [periods_matrix[w2,t] | t in 1..n]))::domain_propagation;
  

  

  
solve satisfy;

output [
  "              " ++ concat([ "Week " ++ show(w) ++ "        " | w in 1..weeks ]) ++ "\n",
  "           " ++ concat([ "-" | i in 1..weeks * 14 ]) ++ "\n"
] ++
[
  "Period " ++ show(p) ++ ": |" ++
  concat([
    let {
      array[int] of int: idxs = [i | i in 1..n where fix(periods_matrix[w,i] mod periods) == p mod periods]
    } in
    if length(idxs) == 2 then
      "    " ++ show(idxs[1]) ++ " v " ++ show(fix(matches[w,idxs[1]])) ++ "    |"
    else
      "              |"
    endif
    | w in 1..weeks
  ]) ++ "\n" ++
  "           " ++ concat([ "-" | i in 1..weeks * 14 ]) ++ "\n"
  | p in 1..periods
];
  
