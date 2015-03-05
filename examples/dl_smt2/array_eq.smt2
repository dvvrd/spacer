;
; B (x , x).
; false :- in[j] > 0 ,  B(in, out), in[out] < 0.
;
(declare-var j Int)
(declare-var in (Array Int Int))
(declare-var out (Array Int Int))

(declare-rel B ((Array Int Int) (Array Int Int)))

(rule (B in in))
(query (and
        (B in out)
        (< (select in j) 0)
        (> (select out j) 0)))
