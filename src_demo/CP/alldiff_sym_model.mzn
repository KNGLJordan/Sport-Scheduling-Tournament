% alldiff_sym model

include "alldifferent.mzn";

int: n; % number of queens
array[1..n] of var 1..n: q; %variables & domains 

%column attack constraints
constraint alldifferent(q)::domain_propagation;

%diagonal attack constraints
constraint alldifferent([q[i]+i | i in 1..n])::domain_propagation;
constraint alldifferent([q[i]-i | i in 1..n])::domain_propagation;

%dual model 
include "lex_lesseq.mzn";
array[1..n, 1..n] of var bool: qb; %dual variables & domains 

%chanelling constraints
constraint forall(i,j in 1..n)(q[i] = j <-> qb[i,j]=1)::domain_propagation;

%symmetry breaking constraints 
constraint 
    lex_lesseq(array1d(qb), [ qb[j,i] | i,j in 1..n ])
/\  lex_lesseq(array1d(qb), [ qb[i,j] | i in reverse(1..n), j in 1..n ])
/\  lex_lesseq(array1d(qb), [ qb[j,i] | i in 1..n, j in reverse(1..n) ])
/\  lex_lesseq(array1d(qb), [ qb[i,j] | i in 1..n, j in reverse(1..n) ])
/\  lex_lesseq(array1d(qb), [ qb[j,i] | i in reverse(1..n), j in 1..n ])
/\  lex_lesseq(array1d(qb), [ qb[i,j] | i,j in reverse(1..n) ])
/\  lex_lesseq(array1d(qb), [ qb[j,i] | i,j in reverse(1..n) ])
;

%Search
solve satisfy;