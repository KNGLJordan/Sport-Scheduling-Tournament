# Gurobi 12.0.2:   lim:time = 300

# n = 6: 0.055 sec.
# n = 8: 0.136 sec.
# n = 10: 14.988 sec.
# n = 12: 107.012 sec.
# n = 14: 300.872 sec.

# cbc 2.10.12:   double:seconds = 300


# CPLEX 22.1.2:   lim:time = 300


# HiGHS 1.11.0:   lim:time = 300



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

# ---------------------------- MATCHES MATRIX ----------------------------------------------------------------

#every team plays with every other team only once
subject to AllDifferentMatches{t1 in Teams, t2 in Teams: t1 != t2}:
    sum{w in WeekVals} m_enc[w, t1, t2] <= 1;

# every team plays once a week
subject to OneGamePerWeek{w in WeekVals, t1 in Teams}:
    sum{t2 in Teams: t2 != t1} m_enc[w, t1, t2] = 1;

subject to symmetry{t1 in Teams, t2 in Teams, w in WeekVals: t1 < t2}:
    m_enc[w,t1,t2] = m_enc[w,t2,t1];

# ---------------------------- PERIODS MATRIX ---------------------------------------------------------------

# every team plays at most twice in the same period over the tournament  

subject to MaxTwoPeriods{t in Teams, p in PeriodVals}:
    sum{w in WeekVals} p_enc[w, t, p] <= 2;

# every week have exactly two periods

subject to ExactlyTwoPeriodsPerWeek{w in WeekVals, p in PeriodVals}:
    sum{t in Teams} p_enc[w, t, p] = 2;

# -------------------- SAME MATCH => SAME PERIOD --------------------------------------------------------

subject to same_period_for_match{t1 in Teams, t2 in Teams, w in WeekVals, p in PeriodVals: t1 < t2}:
    p_enc[w,t1,p] - p_enc[w,t2,p] <= 1 - m_enc[w,t1,t2];




