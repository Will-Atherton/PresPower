; sat
(set-logic ALL)
(declare-fun x () Int)
(declare-fun y () Int)

(assert (>= y 0))
(assert (or (= x (pow y 2)) (< y 0)))
(assert (<= x y))
(assert (=> (< x y) (> x y)))
(assert (ite (<= x y) true false))

(check-sat)