(declare-var x Real)
(declare-var y Real)
(declare-var z Real)
(declare-var x1 Real)
(declare-var y1 Real)
(declare-var z1 Real)

(declare-rel L1 (Real Real Real))
(declare-rel L2 (Real Real Real))
(declare-rel F (Real Real Real))
(declare-rel G (Real Real))
(declare-rel E ())

(rule
    (=> (and (= x 0) (= y 0) (= z 0))
        (L1 x y z)
    )
)

(rule
    (=> (and (L1 x y z) (= x1 (+ x 1)) (= y1 (+ y 1)) (= z1 (- z 2)))
        (L1 x1 y1 z1)
    )
)

(rule
    (=> (L1 x y z)
        (L2 x y z)
    )
)

(rule
    (=> (and (L2 x y z) (= x1 (- x 1)) (= y1 (- y 3)) (= z1 (+ z 2)))
        (L2 x1 y1 z1)
    )
)

(rule
    (=> (L2 x y z)
        (F x y z)
    )
)

(rule
    (=> (= x1 (+ x 1))
        (G x x1)
    )
)

(rule
    (=> (and (F x y z) (G x x1) (or (not (= (+ (* 2 x) z) 0)) (> y (- x1 1))))
        E
    )
)

(query E)
