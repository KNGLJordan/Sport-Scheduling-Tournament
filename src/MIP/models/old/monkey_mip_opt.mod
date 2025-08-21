
param n;
param weeks := n - 1;
param periods := n div 2;

set Teams := 1..n;
set WeekVals := 1..weeks;    
set PeriodVals := 1..periods;

# unary encoding for matches
var m_enc{w in WeekVals, i in Teams, j in Teams} binary;
var matches{w in WeekVals, i in Teams} integer;

subject to OneHotMatch{w in WeekVals, i in Teams}:
    sum{j in Teams} m_enc[w,i,j] = 1;

subject to EncodeMatch{w in WeekVals, i in Teams}:
    matches[w,i] = sum{j in Teams} j * m_enc[w,i,j];

# unary encoding for periods_matrix
var p_enc{w in WeekVals, i in Teams, p in PeriodVals} binary;
var periods_matrix{w in WeekVals, i in Teams} integer;

subject to OneHotPeriod{w in WeekVals, i in Teams}:
    sum{p in PeriodVals} p_enc[w,i,p] = 1;

subject to EncodePeriod{w in WeekVals, i in Teams}:
    periods_matrix[w,i] = sum{p in PeriodVals} p * p_enc[w,i,p];

# unary encoding for home/away matrix
var home_matrix {w in WeekVals, i in Teams} binary;

# ---------------------- OBJECTIVE FUNCTION ---------------------------------------------------------------

# ## OBJ 1: min max h_t
# var home_matches {t in Teams} integer, >= 0, <= weeks;

# subject to HomeMatchCalculation {t in Teams}:
#     home_matches[t] = sum{w in WeekVals} home_matrix[w,t];

# var b_max {t in Teams} binary;
# var max_home_matches integer, >= periods, <= weeks;

# subject to OnlyOneMax:
#     sum {t in Teams} b_max[t] = 1;

# subject to MaxIsGreater {t in Teams}:
#     max_home_matches >= home_matches[t];

# subject to MaxSelector {t in Teams}:
#     max_home_matches <= home_matches[t] + (2 * weeks) * (1 - b_max[t]);

# minimize Unbalance:
#     max_home_matches;

## OBJ 2: min max |d_t| = min max |2 * h_t - WEEKS|
var balance {t in Teams} integer, >= -weeks, <= weeks;

subject to BalanceCalculation {t in Teams}:
    balance[t] = 2 * sum {w in WeekVals} home_matrix[w,t] - weeks;

var abs_balance {t in Teams} integer, >= 0, <= weeks;
var b_abs {t in Teams} binary;

# abs of balances
# abs_balance[t] = |balance[t]| = max{balance[t], -balance[t]}
subject to GreaterX {t in Teams}:
    abs_balance[t] >= balance[t];

subject to GreaterNegativeX {t in Teams}:
    abs_balance[t] >= -balance[t];

subject to XSelector {t in Teams}:
    abs_balance[t] <= balance[t] + (2 * weeks) * (1 - b_abs[t]);

subject to NegativeXSelector {t in Teams}:
    abs_balance[t] <= -balance[t] + (2 * weeks) * b_abs[t];


var b_max {t in Teams} binary;
var max_abs_balance integer, >= 1, <= weeks;

subject to OnlyOneMax:
    sum {t in Teams} b_max[t] = 1;

subject to MaxIsGreater {t in Teams}:
    max_abs_balance >= balance[t];

subject to MaxSelector {t in Teams}:
    max_abs_balance <= balance[t] + (2 * weeks) * (1 - b_max[t]);

minimize Unbalance:
    max_abs_balance;

# ---------------------------- MATCHES MATRIX ----------------------------------------------------------------

#every team plays with every other team only once
subject to AllDifferentMatches{t1 in Teams, t2 in Teams: t1 != t2}:
    sum{w in WeekVals} m_enc[w, t1, t2] <= 1;

# every team plays once a week
subject to OneGamePerWeek{w in WeekVals, t1 in Teams}:
    sum{t2 in Teams: t2 != t1} m_enc[w, t1, t2] = 1;

# the matches are symmetric (if 1 plays against 2 on week 1, then also 2 plays against 1 on week 1)
subject to MatchesSymmetry{t1 in Teams, t2 in Teams, w in WeekVals: t1 < t2}:
    m_enc[w,t1,t2] = m_enc[w,t2,t1];

# ---------------------------- PERIODS MATRIX ---------------------------------------------------------------

# every team plays at most twice in the same period over the tournament  
subject to MaxTwoPeriods{t in Teams, p in PeriodVals}:
    sum{w in WeekVals} p_enc[w, t, p] <= 2;

# every week have exactly two periods
subject to ExactlyTwoPeriodsPerWeek{w in WeekVals, p in PeriodVals}:
    sum{t in Teams} p_enc[w, t, p] = 2;

# ---------------------------- HOME/AWAY MATRIX -------------------------------------------------------------

# same match have 1 home team and 1 away team (SameMatchDifferentHome)
subject to SMDHLowerBound{t1 in Teams, t2 in Teams, w in WeekVals: t1 < t2}:
    home_matrix[w,t1] + home_matrix[w,t2] >= m_enc[w,t1,t2];

subject to SMDHUpperBound{t1 in Teams, t2 in Teams, w in WeekVals: t1 < t2}:
    home_matrix[w,t1] + home_matrix[w,t2] <= 2 - m_enc[w,t1,t2];

# -------------------- SAME MATCH => SAME PERIOD --------------------------------------------------------

subject to SameMatchSamePeriod{t1 in Teams, t2 in Teams, w in WeekVals, p in PeriodVals: t1 < t2}:
    p_enc[w,t1,p] - p_enc[w,t2,p] <= 1 - m_enc[w,t1,t2];




