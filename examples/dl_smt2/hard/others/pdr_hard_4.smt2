(declare-var x Real)
(declare-var y Real)
(declare-var x1 Real)
(declare-var x2 Real)
(declare-var y1 Real)
(declare-var i Real)
(declare-var i1 Real)
(declare-var n Real)
(declare-var m Real)

(declare-rel L1 (Real Real Real))
(declare-rel F (Real Real Real))
(declare-rel G (Real Real Real))
(declare-rel E ())

(rule
    (=> (and (= x 0) (= y 0) (> n 0))
        (L1 x y n)
    )
)

(rule
    (=> (and (L1 x y n) (< x n) (= x1 (+ x 1)) (= y1 (+ y 1)))
        (L1 x1 y1 n)
    )
)

(rule
    (=> (and (L1 x y n) (>= x n))
        (F x y n)
    )
)

;(rule
;    (=> (= x1 (+ x 1))
;        (G x x1)
;    )
;)

(rule
    (=> (and (< x n) (= x1 (+ x 1)))
        (G x x1 n)
    )
)

(rule
    (=> (and (G (- x 1) x1 n) (>= x n) (= x2 (+ x1 1)))
        (G x x2 n)
    )
)

(rule
    (=> (and (F x y n) (G x x1 m) (> n 0) (> m 0) (> y x1))
        E
    )
)

(query E)
