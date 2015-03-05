;
; same as array_eq but with recursion to prevent inlining
;
(declare-var x Int)
(declare-var y Int)
(declare-var j Int)
(declare-var in (Array Int Int))
(declare-var out (Array Int Int))

(declare-rel B (Int (Array Int Int) (Array Int Int)))

(rule (B 0 in in))
(rule (=> (B x in out) (B (+ 1 x) in out)))
(query (and
        (B j in out)
        (< (select in j) 0)
        (> (select out j) 0)))
