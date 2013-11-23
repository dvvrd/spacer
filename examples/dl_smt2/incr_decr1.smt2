(declare-var x Int)
(declare-var y Int)
(declare-var z Int)
(declare-var n Int)
(declare-var x1 Int)
(declare-var y1 Int)

(declare-rel IL (Int Int))
(declare-rel DL (Int Int Int))
(declare-rel F (Int Int))
(declare-rel G (Int Int))
(declare-rel E ())

; incr x from 0 to n; decr x from 2n to n
(rule (=> (and (= x 0) (> n 0)) (IL x n)))
(rule (=> (and (IL x n) (< x n) (= x1 (+ x 1))) (IL x1 n)))
(rule (=> (and (IL x n) (>= x n) (= y (* 2 n))) (DL x y n)))
(rule (=> (and (DL x y n) (> y n) (= y1 (- y 1))) (DL x y1 n)))
(rule (=> (and (DL x y n) (<= y n)) (F x y)))

(rule (=> (= y x) (G x y)))

(rule (=> (and (F x y) (G y z) (not (= x z))) E))

(query E)
