; Tournament scheduling - Decision problem 1
; n=4, weeks=3, periods=2

(set-option :produce-models true)
(set-option :timeout 300000)
(set-logic QF_LIA)

; Variables M[i,j] - week when team i plays team j
; Variables P[i,j] - period when team i plays team j
(declare-fun M_0_1 () Int)
(declare-fun P_0_1 () Int)
(declare-fun M_0_2 () Int)
(declare-fun P_0_2 () Int)
(declare-fun M_0_3 () Int)
(declare-fun P_0_3 () Int)
(declare-fun M_1_2 () Int)
(declare-fun P_1_2 () Int)
(declare-fun M_1_3 () Int)
(declare-fun P_1_3 () Int)
(declare-fun M_2_3 () Int)
(declare-fun P_2_3 () Int)

; Domain constraints
(assert (and (>= M_0_1 0) (< M_0_1 3)))
(assert (and (>= P_0_1 0) (< P_0_1 2)))
(assert (and (>= M_0_2 0) (< M_0_2 3)))
(assert (and (>= P_0_2 0) (< P_0_2 2)))
(assert (and (>= M_0_3 0) (< M_0_3 3)))
(assert (and (>= P_0_3 0) (< P_0_3 2)))
(assert (and (>= M_1_2 0) (< M_1_2 3)))
(assert (and (>= P_1_2 0) (< P_1_2 2)))
(assert (and (>= M_1_3 0) (< M_1_3 3)))
(assert (and (>= P_1_3 0) (< P_1_3 2)))
(assert (and (>= M_2_3 0) (< M_2_3 3)))
(assert (and (>= P_2_3 0) (< P_2_3 2)))

; Constraint 1: Every team plays once a week
(assert (= (+ (ite (= M_0_1 0) 1 0) (ite (= M_0_2 0) 1 0) (ite (= M_0_3 0) 1 0)) 1))
(assert (= (+ (ite (= M_0_1 1) 1 0) (ite (= M_0_2 1) 1 0) (ite (= M_0_3 1) 1 0)) 1))
(assert (= (+ (ite (= M_0_1 2) 1 0) (ite (= M_0_2 2) 1 0) (ite (= M_0_3 2) 1 0)) 1))
(assert (= (+ (ite (= M_0_1 0) 1 0) (ite (= M_1_2 0) 1 0) (ite (= M_1_3 0) 1 0)) 1))
(assert (= (+ (ite (= M_0_1 1) 1 0) (ite (= M_1_2 1) 1 0) (ite (= M_1_3 1) 1 0)) 1))
(assert (= (+ (ite (= M_0_1 2) 1 0) (ite (= M_1_2 2) 1 0) (ite (= M_1_3 2) 1 0)) 1))
(assert (= (+ (ite (= M_0_2 0) 1 0) (ite (= M_1_2 0) 1 0) (ite (= M_2_3 0) 1 0)) 1))
(assert (= (+ (ite (= M_0_2 1) 1 0) (ite (= M_1_2 1) 1 0) (ite (= M_2_3 1) 1 0)) 1))
(assert (= (+ (ite (= M_0_2 2) 1 0) (ite (= M_1_2 2) 1 0) (ite (= M_2_3 2) 1 0)) 1))
(assert (= (+ (ite (= M_0_3 0) 1 0) (ite (= M_1_3 0) 1 0) (ite (= M_2_3 0) 1 0)) 1))
(assert (= (+ (ite (= M_0_3 1) 1 0) (ite (= M_1_3 1) 1 0) (ite (= M_2_3 1) 1 0)) 1))
(assert (= (+ (ite (= M_0_3 2) 1 0) (ite (= M_1_3 2) 1 0) (ite (= M_2_3 2) 1 0)) 1))

; Constraint 2: Every week has exactly periods matches
(assert (= (+ (ite (= M_0_1 0) 1 0) (ite (= M_0_2 0) 1 0) (ite (= M_0_3 0) 1 0) (ite (= M_1_2 0) 1 0) (ite (= M_1_3 0) 1 0) (ite (= M_2_3 0) 1 0)) 2))
(assert (= (+ (ite (= M_0_1 1) 1 0) (ite (= M_0_2 1) 1 0) (ite (= M_0_3 1) 1 0) (ite (= M_1_2 1) 1 0) (ite (= M_1_3 1) 1 0) (ite (= M_2_3 1) 1 0)) 2))
(assert (= (+ (ite (= M_0_1 2) 1 0) (ite (= M_0_2 2) 1 0) (ite (= M_0_3 2) 1 0) (ite (= M_1_2 2) 1 0) (ite (= M_1_3 2) 1 0) (ite (= M_2_3 2) 1 0)) 2))

; Constraint 3: Every week and period have exactly one match
(assert (= (+ (ite (and (= M_0_1 0) (= P_0_1 0)) 1 0) (ite (and (= M_0_2 0) (= P_0_2 0)) 1 0) (ite (and (= M_0_3 0) (= P_0_3 0)) 1 0) (ite (and (= M_1_2 0) (= P_1_2 0)) 1 0) (ite (and (= M_1_3 0) (= P_1_3 0)) 1 0) (ite (and (= M_2_3 0) (= P_2_3 0)) 1 0)) 1))
(assert (= (+ (ite (and (= M_0_1 0) (= P_0_1 1)) 1 0) (ite (and (= M_0_2 0) (= P_0_2 1)) 1 0) (ite (and (= M_0_3 0) (= P_0_3 1)) 1 0) (ite (and (= M_1_2 0) (= P_1_2 1)) 1 0) (ite (and (= M_1_3 0) (= P_1_3 1)) 1 0) (ite (and (= M_2_3 0) (= P_2_3 1)) 1 0)) 1))
(assert (= (+ (ite (and (= M_0_1 1) (= P_0_1 0)) 1 0) (ite (and (= M_0_2 1) (= P_0_2 0)) 1 0) (ite (and (= M_0_3 1) (= P_0_3 0)) 1 0) (ite (and (= M_1_2 1) (= P_1_2 0)) 1 0) (ite (and (= M_1_3 1) (= P_1_3 0)) 1 0) (ite (and (= M_2_3 1) (= P_2_3 0)) 1 0)) 1))
(assert (= (+ (ite (and (= M_0_1 1) (= P_0_1 1)) 1 0) (ite (and (= M_0_2 1) (= P_0_2 1)) 1 0) (ite (and (= M_0_3 1) (= P_0_3 1)) 1 0) (ite (and (= M_1_2 1) (= P_1_2 1)) 1 0) (ite (and (= M_1_3 1) (= P_1_3 1)) 1 0) (ite (and (= M_2_3 1) (= P_2_3 1)) 1 0)) 1))
(assert (= (+ (ite (and (= M_0_1 2) (= P_0_1 0)) 1 0) (ite (and (= M_0_2 2) (= P_0_2 0)) 1 0) (ite (and (= M_0_3 2) (= P_0_3 0)) 1 0) (ite (and (= M_1_2 2) (= P_1_2 0)) 1 0) (ite (and (= M_1_3 2) (= P_1_3 0)) 1 0) (ite (and (= M_2_3 2) (= P_2_3 0)) 1 0)) 1))
(assert (= (+ (ite (and (= M_0_1 2) (= P_0_1 1)) 1 0) (ite (and (= M_0_2 2) (= P_0_2 1)) 1 0) (ite (and (= M_0_3 2) (= P_0_3 1)) 1 0) (ite (and (= M_1_2 2) (= P_1_2 1)) 1 0) (ite (and (= M_1_3 2) (= P_1_3 1)) 1 0) (ite (and (= M_2_3 2) (= P_2_3 1)) 1 0)) 1))

; Constraint 4: Every team can have a match in the same period at most two times
(assert (<= (+ (ite (= P_0_1 0) 1 0) (ite (= P_0_2 0) 1 0) (ite (= P_0_3 0) 1 0)) 2))
(assert (<= (+ (ite (= P_0_1 1) 1 0) (ite (= P_0_2 1) 1 0) (ite (= P_0_3 1) 1 0)) 2))
(assert (<= (+ (ite (= P_0_1 0) 1 0) (ite (= P_1_2 0) 1 0) (ite (= P_1_3 0) 1 0)) 2))
(assert (<= (+ (ite (= P_0_1 1) 1 0) (ite (= P_1_2 1) 1 0) (ite (= P_1_3 1) 1 0)) 2))
(assert (<= (+ (ite (= P_0_2 0) 1 0) (ite (= P_1_2 0) 1 0) (ite (= P_2_3 0) 1 0)) 2))
(assert (<= (+ (ite (= P_0_2 1) 1 0) (ite (= P_1_2 1) 1 0) (ite (= P_2_3 1) 1 0)) 2))
(assert (<= (+ (ite (= P_0_3 0) 1 0) (ite (= P_1_3 0) 1 0) (ite (= P_2_3 0) 1 0)) 2))
(assert (<= (+ (ite (= P_0_3 1) 1 0) (ite (= P_1_3 1) 1 0) (ite (= P_2_3 1) 1 0)) 2))

(check-sat)
(get-model)
(exit)