; sat: y = 0, x = 1
(set-logic ALL)
(declare-fun x () Int)
(declare-fun y () Int)

(assert (>= y 0))
(assert (= x (pow y 2)))

(check-sat)