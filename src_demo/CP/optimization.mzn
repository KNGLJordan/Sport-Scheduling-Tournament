include "alldifferent.mzn";
include "globals.mzn";

int: n; % number of teams
int: weeks = n - 1; % number of weeks
int: periods = n div 2; % number of periods

% Decision variables
array[1..weeks, 1..n] of var 1..n: matches; % opponent for each team in each week
array[1..weeks, 1..n] of var 1..periods: periods_matrix; % period for each team in each week
array[1..weeks, 1..n] of var 0..1: home_away; % 1 if team plays at home, 0 if away

% Fix matches for team 1 to reduce symmetry
%Visto che tanto empiricamente abbiamo visto che il team 1 gioca sempre con gli alri team 'in ordine' (prima il team 2, poi 3, etc),
%tanto vale metterlo come constraint così evitiamo che esplori soluzioni diverse da questa 
constraint
  forall(w in 1..weeks)(
    matches[w,1] = w + 1
  );

% IMPLIED: Matches are symmetric (if i plays j, then j plays i)
constraint
  forall(w in 1..weeks, t in 1..n)(
    matches[w, matches[w, t]] = t
  );

% Every team plays with every other team exactly once
constraint
  forall(t in 1..n)(
    alldifferent([t] ++ [matches[w, t] | w in 1..weeks])
  );

% Every team plays exactly once per week
constraint
  forall(w in 1..weeks)(
    alldifferent([matches[w, t] | t in 1..n])
  );

% Every team plays at most twice in the same period over the tournament
constraint 
  forall(t in 1..n, p in 1..periods)(
    count([periods_matrix[w, t] | w in 1..weeks], p) < 3
  );

% Both teams in a match have the same period
constraint
  forall(w in 1..weeks, t in 1..n)(
    periods_matrix[w, t] = periods_matrix[w, matches[w, t]]
  );

% Every period has exactly two teams per week
constraint
  forall(w in 1..weeks, p in 1..periods)(
    count([periods_matrix[w, t] | t in 1..n], p) = 2
  );


% SYMMETRY BREAKING (without forcing home/away assignments)
% 1. Break symmetry by ensuring matches matrix is lexicographically ordered
constraint
  forall(w in 1..weeks-1, w2 in w+1..weeks)(
    lex_lesseq([matches[w, t] | t in 1..n], [matches[w2, t] | t in 1..n])
  );

% 2. Break symmetry for periods
constraint
  forall(w in 1..weeks-1, w2 in w+1..weeks)(
    lex_lesseq([periods_matrix[w, t] | t in 1..n], [periods_matrix[w2, t] | t in 1..n])
  );

% 3. Symmetry breaking for home-away
constraint home_away[1, 1] = 1;
%la simmetria home-away può essere solo 'totale', ovvero che si invertano tutti quanti gli 0 e gli 1. quindi
%è una simmetria molto più facile da rimuovere rispetto alle altre, perchè basta imporre un 1, e la simmetria sarà evitata, perchè lui non può diventare 0 e quindi neanche tutti gli altri si possono invertire.

% HOME/AWAY CONSTRAINTS

% In each match, exactly one team plays at home and one away
constraint
  forall(w in 1..weeks, t in 1..n)(
    home_away[w, t] + home_away[w, matches[w, t]] = 1
  );
% Calculate total home games for each team
array[1..n] of var 0..(n-1): home_games;

constraint
  forall(t in 1..n)(
    home_games[t] = sum(w in 1..weeks)(home_away[w, t])
  );


% Minimize the difference between max and min home games across all teams
var 0..(n-1): max_home_games;
var 0..(n-1): min_home_games;



constraint max_home_games = max(home_games);
constraint min_home_games = min(home_games);

var 1..(n-1): home_balance_range = max_home_games - min_home_games;
%1 is the minimal imbalance, so if we get 1 we are good and we can stop

solve minimize home_balance_range;

% OUTPUT
output [
  "Home/Away Balance:\n"
] ++
[
  "Team " ++ show(t) ++ ": " ++ show(fix(home_games[t])) ++ " home, " ++
  show((n-1) - fix(home_games[t])) ++ " away\n"
  | t in 1..n
] ++
[
  "\nHome game range (max - min): " ++ show(fix(home_balance_range)) ++ "\n\n"
] ++
[
  "              " ++ concat(["Week " ++ show(w) ++ "        " | w in 1..weeks]) ++ "\n",
  "           " ++ concat(["-" | i in 1..weeks * 14]) ++ "\n"
] ++
[
  "Period " ++ show(p) ++ ": |" ++
  concat([
    let {
      array[int] of int: idxs = [i | i in 1..n where fix(periods_matrix[w, i]) == p];
      int: home_team = if length(idxs) == 2 then
        if fix(home_away[w, idxs[1]]) == 1 then idxs[1] else idxs[2] endif
      else 0 endif;
      int: away_team = if length(idxs) == 2 then
        if fix(home_away[w, idxs[1]]) == 0 then idxs[1] else idxs[2] endif
      else 0 endif;
    } in
    if length(idxs) == 2 then
      "    " ++ show(home_team) ++ " v " ++ show(away_team) ++ "    |"
    else
      "              |"
    endif
    | w in 1..weeks
  ]) ++ "\n" ++
  "           " ++ concat(["-" | i in 1..weeks * 14]) ++ "\n"
  | p in 1..periods
];
