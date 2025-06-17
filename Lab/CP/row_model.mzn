% Row model

include "alldifferent.mzn";

int: n; % number of queens
array[1..n] of var 1..n: rows; %variables & domains 

%column attack constraints
constraint alldifferent(rows)::domain_propagation;

%diagonal attack constraints
%we can use also ::domain_propagation (less failures, less time)
constraint forall(i,j in 1..n where i<j)(abs(rows[i] - rows[j]) != abs(i-j)); 


%Search
solve satisfy; 


