;M ()
;    assume n > 0
;    Incr (n, x)
;    Decr (n, y)
;    assert x==y
;
;Incr (n, x)
;    x = 0
;    while x < n:
;        x++
;
;Decr (n, y)
;    y = 2*n
;    while (y > n):
;        y--


(declare-var x Int)
(declare-var y Int)
(declare-var n Int)
(declare-var x1 Int)
(declare-var y1 Int)

(declare-rel IL (Int Int))
(declare-rel I (Int Int))
(declare-rel DL (Int Int))
(declare-rel D (Int Int))
(declare-rel E ())

(rule (=> (and (> y 0) (= x 0)) (IL x n)))
(rule (=> (and (IL x n) (< x n) (= x1 (+ x 1))) (IL x1 n)))
(rule (=> (and (IL x n) (>= x n)) (I n x)))

(rule (=> (= y (* 2 n)) (DL y n)))
(rule (=> (and (DL y n) (> y n) (= y1 (- y 1))) (DL y1 n)))
(rule (=> (and (DL y n) (<= y n)) (D n y)))

(rule (=> (and (I n x) (D n y) (> n 0) (not (= x y))) E))

(query E)
