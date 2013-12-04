; example from bebop paper

; decl g

; void main ()
;   level1 ()
;   level1 ()
;   if (!g)
;       reach:

; Level<i>
;   decl a b c
;   if (g)
;       a,b,c := 0,0,0
;       while (!a | !b | !c)
;           if (!a)
;               a := 1
;           else if (!b)
;               a,b := 0,1
;           else if (!c)
;               a,b,c := 0,0,1
;   else
;       Level<i+1>; Level<i+1>
;   g := !g

(declare-var a Bool)
(declare-var b Bool)
(declare-var c Bool)
(declare-var g1 Bool)
(declare-var g2 Bool)
(declare-var g3 Bool)
(declare-var n Int)
(declare-var N Int)

(declare-rel L (Bool Bool Bool Int))
(declare-rel Lvl (Bool Bool Int Int))
(declare-rel E ())

(rule (L false false false n))

(rule (=> (and (L a b c n)
               (not a))
          (L true b c n)))

(rule (=> (and (L a b c n)
               a
               (not b))
          (L false true c n)))

(rule (=> (and (L a b c n)
               a b
               (not c))
          (L false false true n)))

(rule (=> (L true true true n)
          (Lvl true false n N)))

(rule (Lvl false true 0 N))

(rule (=> (and (Lvl false g1 (- n 1) N)
               (Lvl g1 g2 (- n 1) N)
               (> n 0))
          (Lvl false (not g2) n N)))

(rule (=> (and (Lvl g1 g2 N N)
               (Lvl g2 g3 N N)
               (> N 0)
               (not (= g1 g3)))
          E))

(query E)
