% CHUFFED 0.13.2
% n = 8: balance score = 0 in 993msec., nSolution = 3
% n = 10: balance score = 2 in 5m 0s., nSolution = 5

include "globals.mzn";

int: n; % number of teams
int: weeks = n-1;
int: periods = n div 2; % number of periods

array[1..weeks,1..periods, 1..2] of var 1..n: tournament; % matrix for tournament

% unbalance score = sum of abs difference between home and away matches for each team
% NOTE: every team plays n-1 matches; since n-1 is an odd number, the contribution to the sum for each team is at least 1
% IMPLICATION: it's possible to substract n to the balance_score so that the lower bound is 0 
var int: unbalance_score =
  sum([
    abs(
      sum([
        if tournament[i,j,1] == t then 1 else 0 endif +
        if tournament[i,j,2] == t then -1 else 0 endif
        | i in 1..weeks, j in 1..periods
      ])
    )
    | t in 1..n
  ]) - n;


% every team plays with every other team only once
constraint
  forall(t in 1..n)( alldifferent([ tournament[i, j, k] | i in 1..weeks, j in 1..periods, k in 1..2 
                                                          where (k == 1 /\ tournament[i,j,2] == t) \/ (k == 2 /\ tournament[i,j,1] == t) ]) );

% every team plays once a week
constraint 
  forall(i in 1..weeks)(alldifferent([tournament[i, j, k] | j in 1..periods, k in 1..2]));

% every team plays at most twice in the same period over the tournament
constraint 
  forall(t in 1..n, j in 1..periods)(count([tournament[i, j, k] | i in 1..weeks, k in 1..2], t) < 3);

% NOTE: thanks to the lower bound equal to 0, we can minimize the abs of unbalance_Score so that if it reaches 0 the search terminates
solve minimize abs(unbalance_score);

output [

  % Intestazione con nomi delle settimane
  "              " ++
  concat([ "Week " ++ show(w) ++ "        " | w in 1..weeks ]) ++ "\n" ++

  % Riga di separazione iniziale
  "           " ++ concat([ "--------------" | w in 1..weeks ]) ++ "\n" ++

  % Corpo della tabella
  concat([
    "Period " ++ show(p) ++ ": |   " ++
    concat([
      " " ++ show(tournament[w,p,1]) ++ " v " ++ show(tournament[w,p,2]) ++ "    |   "
      | w in 1..weeks
    ]) ++ "\n" ++
    "           " ++ concat([ "--------------" | w in 1..weeks ]) ++ "\n"
    | p in 1..periods
  ])
  
  % Balance score
  ++"\nBalance score: " ++ show(unbalance_score) ++ "\n"
];

