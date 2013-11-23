(declare-var n Real)
(declare-var n0 Real)
(declare-var n1 Real)
(declare-var n2 Real)
(declare-var n3 Real)

(declare-rel L (Real Real))
(declare-rel G (Real Real))
(declare-rel E ())

(rule
    (=> (<= n 0)
        (L n n)
    )
)

(rule
    (=> (and (L n2 n3) (> n0 0) (= n2 (- n0 2)) (= n1 (+ n3 1)))
        (L n0 n1)
    )
)

(rule
    (=> (= n1 (- n0 1))
        (G n0 n1)
    )
)

(rule
    (=> (and (L n0 n1) (G n1 n2) (< n0 (+ (* 2 n2) 2)))
        E
    )
)

(query E)
