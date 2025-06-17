% alldiff model

include "alldifferent.mzn";

int: n; % number of queens
array[1..n] of var 1..n: q; %variables & domains

var int: obj = sum(i in 1..n)(abs(q[i]-i)); % for Optimal-NQueens

%column attack constraints
constraint alldifferent(q)::domain_propagation;

%diagonal attack constraints
constraint alldifferent([q[i]+i | i in 1..n])::domain_propagation;
constraint alldifferent([q[i]-i | i in 1..n])::domain_propagation;

%Search
%solve satisfy; 

%Search with different techniques of randomization + restart
%solve :: int_search(q, input_order, indomain_min) satisfy;
%solve :: int_search(q, input_order, indomain_random) satisfy;
%solve :: int_search(q, first_fail, indomain_min) satisfy;
%solve :: int_search(q, first_fail, indomain_random) satisfy;
%solve :: int_search(q, dom_w_deg, indomain_min) satisfy;
%solve :: int_search(q, dom_w_deg, indomain_random) satisfy;

% COMMENTS: in this case domWdeg doesn't show any difference because in the weighted sum the weights are all equals.
% This beacuse all the variables appears in all the constraints and so the weights are equivalent.

% Relax and reconstruct Annotation to minimize Optimal-NQueens
%solve minimize obj;
%solve :: int_search(q, dom_w_deg, indomain_random) minimize obj;
%solve :: int_search(q, dom_w_deg, indomain_random)::restart_luby(250) minimize obj;
solve :: int_search(q, dom_w_deg, indomain_random)::restart_luby(250)::relax_and_reconstruct(q,85) minimize obj;

output["obj = \(obj)\n"];