% CHUFFED 0.13.2
% n = 12: 1s 190msec.
% n = 14: 27s 301msec.
% n = 16: Time limit

include "globals.mzn";

int: n; % number of teams
int: weeks = n-1; % number of weeks
int: periods = n div 2; % number of periods

array[1..weeks, 1..n] of var 1..n: matches; % for every team and week, the opponent
array[1..weeks, 1..n] of var 1..periods: periods_matrix;  % for every team and week, the period of the match

% CONSTRAINT
% every team plays with every other team only once
constraint
  forall(t in 1..n)(alldifferent([t] ++ [matches[w, t] | w in 1..weeks]));
  
% every team plays once a week
constraint
  forall(w in 1..weeks)(alldifferent([matches[w, t] | t in 1..n]));
  
% % every match is symmetric (implicit?)
% constraint
%   forall(w in 1..weeks, t in 1..n)(matches[w, matches[w, t]] = t);
  
% every team plays at most twice in the same period over the tournament  
constraint 
  forall(t in 1..n, p in 1..periods)(count([periods_matrix[w, t] | w in 1..weeks], p) < 3);

% both team of a match have the same period
constraint
  forall(w in 1..weeks, t in 1..n)(periods_matrix[w, t] = periods_matrix[w, matches[w, t]]);

% every period have exactly two teams per week
constraint
  forall(w in 1..weeks, p in 1..periods)(count([periods_matrix[w, t] | t in 1..n], p) = 2);
  
% SYMMETRY BREAKING
% symmetry beaking constraint: we impose the columns of the matrix matches to be in lex order
constraint
  forall(w in 1..weeks-1, w2 in w+1..weeks)(lex_lesseq([matches[w,t] | t in 1..n], [matches[w2,t] | t in 1..n]));

% symmetry breaking for periods
constraint
  forall(w in 1..weeks-1, w2 in w+1..weeks)(lex_lesseq([periods_matrix[w,t] | t in 1..n], [periods_matrix[w2,t] | t in 1..n]));  

  
solve satisfy;

output [
  "              " ++ concat([ "Week " ++ show(w) ++ "        " | w in 1..weeks ]) ++ "\n",
  "           " ++ concat([ "-" | i in 1..weeks * 14 ]) ++ "\n"
] ++
[
  "Period " ++ show(p) ++ ": |" ++
  concat([
    let {
      array[int] of int: idxs = [i | i in 1..n where fix(periods_matrix[w,i]) == p]
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
  
%   % ----------- For Debug ----------- %
%   ] ++ [
%   % ----------- Matches matrix (w x n) ----------- %
%   "\n\nWeeks Matrix:\n" ++
%   concat([ concat([ show(fix(matches[i,j])) ++ " " | j in 1..n ]) ++ "\n" | i in 1..weeks ]) ++

%   % ----------- Periods matrix (w x n) ----------- %
%   "\nPeriods Matrix:\n" ++
%   concat([ concat([ show(fix(periods_matrix[i,j])) ++ " " | j in 1..n ]) ++ "\n" | i in 1..weeks ])
];
  