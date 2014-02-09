;;;
;;; An example showing divergence of GPDR engine of Z3
;;;
(set-option :fixedpoint.engine pdr)
(set-option :fixedpoint.inline_eager false)
(declare-var x Real)
(declare-var y Real)
(declare-var x1 Real)
(declare-var y1 Real)
(declare-var i Real)
(declare-var i1 Real)
(declare-var n Real)

(declare-rel L (Real Real Real Real))
(declare-rel G (Real Real))
(declare-rel E ())

(rule
    (=> (and (= x 0) (= y 0) (= i 0))
        (L x y i n)
    )
)

(rule
    (=> (and (L x y i n) (= x1 (+ x 1)) (= y1 (+ y 1)) (= i1 (+ i 1)))
        (L x1 y1 i1 n)
    )
)

(rule
    (=> (= x1 (+ x 1))
        (G x x1)
    )
)

(rule
    (=> (and (L x y n n) (G x x1) (> n 0) (> y x1))
        E
    )
)

(query E)
