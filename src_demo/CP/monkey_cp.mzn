include "alldifferent.mzn";

int: n; % number of teams
int: weeks = n-1;
int: periods = n div 2; % number of periods

array[1..weeks, 1..n] of var 1..n: matches;
array[1..weeks, 1..n] of var 1..periods: periods_matrix;


constraint
  forall(t in 1..n)(alldifferent([t] ++ [matches[w, t] | w in 1..weeks]));
  
  
constraint
  forall(w in 1..weeks)(alldifferent([matches[w, t] | t in 1..n]));
  
constraint 
  forall(t in 1..n, p in 1..periods)(count([periods_matrix[w, t] | w in 1..weeks], p) < 3);
 
constraint
  forall(w in 1..weeks, t in 1..n)(periods_matrix[w, t] = periods_matrix[w, matches[w, t]]);
  
constraint
  forall(w in 1..weeks, p in 1..periods)(count([periods_matrix[w, t] | t in 1..n], p) = 2);

  
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
];
  