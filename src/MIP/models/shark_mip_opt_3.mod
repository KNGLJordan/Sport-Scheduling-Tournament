
param n;
param weeks := n - 1;
param periods := n div 2;

set Teams := 1..n;
set WeekVals := 0..weeks;    
set PeriodVals := 0..periods;

# unary encoding for weeks_matrix

var w_enc{i in Teams, j in Teams, w in WeekVals} binary; # binary or integer??? TO-THINK
var weeks_matrix{i in Teams, j in Teams} integer;

subject to OneHotWeek{i in Teams, j in Teams}:
    sum{w in WeekVals} w_enc[i,j,w] = 1;

subject to EncodeWeek{i in Teams, j in Teams}:
    weeks_matrix[i,j] = sum{w in WeekVals} w * w_enc[i,j,w];

# unary encoding for periods_matrix

var p_enc{i in Teams, j in Teams, p in PeriodVals} binary; # binary or integer??? TO-THINK
var periods_matrix{i in Teams, j in Teams} integer;

subject to OneHotPeriod{i in Teams, j in Teams}:
    sum{p in PeriodVals} p_enc[i,j,p] = 1;

subject to EncodePeriod{i in Teams, j in Teams}:
    periods_matrix[i,j] = sum{p in PeriodVals} p * p_enc[i,j,p];

# unary encoding for home/away matrix

var home_matrix {i in Teams, j in Teams} binary;

# ---------------------- OBJECTIVE FUNCTION ---------------------------------------------------------------

# Minimize the sum over teams of the absolute value of the sum of each row (excluding diagonal)
# (n can be substracted since the lower bound is n, which is the number of teams)

var balance {t in Teams} integer, >= -periods, <= periods;

subject to BalanceCalculation {t1 in Teams}:
    balance[t1] = 2 * sum {t2 in Teams} home_matrix[t1,t2] - weeks;

var b_max {t in Teams} binary;
var b_min {t in Teams} binary;
var max_balance;
var min_balance;

subject to only_one_b_max:
    sum {t in Teams} b_max[t] = 1;

subject to max_balance_is_greater {t in Teams}:
    max_balance >= balance[t];

subject to max_selector {t in Teams}:
    max_balance <= balance[t] + (2 * periods) * (1 - b_max[t]);


subject to only_one_b_min:
    sum {t in Teams} b_min[t] = 1;

subject to min_balance_is_lower {t in Teams}:
    min_balance <= balance[t];

subject to min_selector {t in Teams}:
    min_balance >= balance[t] - (2 * periods) * (1 - b_min[t]);

minimize Unbalance:
    max_balance - min_balance - 2;


# ---------------------- DIAGONALS TO ZERO ----------------------------------------------------------------

# a team does not play against itself in any week

subject to DiagonalWeek{i in Teams}:
    w_enc[i,i,0] = 1;

subject to NoOtherWeek{i in Teams, w in WeekVals: w != 0}:
    w_enc[i,i,w] = 0;

# a team does not play against itself in any period

subject to DiagonalPeriod{i in Teams}:
    p_enc[i,i,0] = 1;

subject to NoOtherPeriod{i in Teams, p in PeriodVals: p != 0}:
    p_enc[i,i,p] = 0;

subject to DiagonalHome{i in Teams}:
    home_matrix[i,i] = 0; 

# ---------------------------- WEEKS MATRIX ----------------------------------------------------------------

#every team plays with every other team only once and plays once a week

subject to AllDifferentWeeksNoDiag{t1 in Teams, w in WeekVals}:
    sum{t2 in Teams: t2 != t1} w_enc[t1, t2, w] <= 1;

# the matches are symmetric (if 1 plays against 2 on week 1, then also 2 plays against 1 on week 1)

subject to WeeksSymmetry{t1 in Teams, t2 in Teams, w in WeekVals: t1 < t2}:
    w_enc[t1, t2, w] = w_enc[t2, t1, w];

# every match is on a valid week

subject to NoZeroWeekMatch{t1 in Teams, t2 in Teams: t1 != t2}:
    w_enc[t1, t2, 0] = 0;

# ---------------------------- PERIODS MATRIX ---------------------------------------------------------------

# every team plays at most twice in the same period over the tournament  

subject to MaxTwoPeriods{t1 in Teams, p in PeriodVals}:
    sum{t2 in Teams: t2 != t1} p_enc[t1, t2, p] <= 2;

# the matches are symmetric (if 1 plays against 2 on period 1, then also 2 plays against 1 on period 1)

subject to PeriodsSymmetry{t1 in Teams, t2 in Teams, p in PeriodVals: t1 < t2}:
    p_enc[t1, t2, p] = p_enc[t2, t1, p];

# every match is on a valid period

subject to NoZeroPeriodMatch{t1 in Teams, t2 in Teams: t1 != t2}:
    p_enc[t1, t2, 0] = 0;

# % every period have the same number of matches
subject to MatchesPerPeriod{p in PeriodVals: p > 0}:
    sum {t1 in Teams, t2 in Teams: t1 != t2} p_enc[t1, t2, p] = weeks * 2;

# ---------------------------- HOME/AWAY MATRIX -------------------------------------------------------------

# the matches are symmetric (if 1 plays at home against 2, then also 2 plays away against 1)
subject to HomeAwaySymmetry{t1 in Teams, t2 in Teams: t1 != t2}:
    home_matrix[t1, t2] + home_matrix[t2, t1] = 1;

# -------------------- SAME WEEK => DIFFERENT PERIOD --------------------------------------------------------

# creating the channeling between weeks and periods

var z_enc{t1 in Teams, t2 in Teams, w in WeekVals, p in PeriodVals: t1 < t2} binary;

# encoding of the AND relation 

# C1 /\ C2
# becomes
# b1 <= b, b2 <= b, b1 + b2 <= b +1 

subject to LinkZ1{t1 in Teams, t2 in Teams, w in WeekVals, p in PeriodVals: t1 < t2}:
    z_enc[t1,t2,w,p] <= w_enc[t1,t2,w];

subject to LinkZ2{t1 in Teams, t2 in Teams, w in WeekVals, p in PeriodVals: t1 < t2}:
    z_enc[t1,t2,w,p] <= p_enc[t1,t2,p];

subject to LinkZ3{t1 in Teams, t2 in Teams, w in WeekVals, p in PeriodVals: t1 < t2}:
    w_enc[t1,t2,w] + p_enc[t1,t2,p] <= z_enc[t1,t2,w,p] + 1;

# all the matches played in the same week have to be in different periods

subject to AlldifferentPeriodsPerWeek{w in WeekVals, p in PeriodVals}:
    sum{t1 in Teams, t2 in Teams: t1 < t2} z_enc[t1,t2,w,p] <= 1;



