% Alldiff decomposition model

include "alldifferent.mzn";

int: n ; % number of queens
array [1..n] of var 1..n: q; % variables & domains 


% aldiff decomposition

% column attack constraints
constraint forall(i,j in 1..n where i<j)(q[i] != q[j]);

%diagonal attack contraints
constraint forall(i,j in 1..n where i<j)(q[i]+i != q[j]+j);
constraint forall(i,j in 1..n where i<j)(q[i]-i != q[j]-j);

solve :: int_search(q, input_order, indomain_min)  satisfy;

