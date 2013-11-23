;0: int x=0; y=0; z=0; w=0;
;1: while (*) {
;2:   if (*)
;3:     {x = x+1; y = y+100;}
;4:   else if (*) {
;5:     if (x >= 4)
;6:       {x = x+1; y = y+1;}
;     }
;---------------------------------------
;7:   else if (y > 10*w && z >= 100*x)
;8:     {y = -y;}
;9a:  t = 1
;9:   w = w+t; z = z+10*t;
;---------------------------------------
;   } 
;10:if (x >= 4 && y <= 2)
;11:  error();


(declare-var x Real)
(declare-var y Real)
(declare-var z Real)
(declare-var w Real)
(declare-var x1 Real)
(declare-var y1 Real)
(declare-var z1 Real)
(declare-var w1 Real)

(declare-var t Real)

(declare-rel L (Real Real Real Real))
(declare-rel T (Real))
(declare-rel entry ())
(declare-rel E ())


(rule (=> true entry))
(rule (=> (and entry (= x 0.0) (= y 0.0) (= z 0.0) (= w 0.0)) (L x y z w)))
(rule (=> (= t 1.0) (T t)))
;(rule (=> (and (>= t 1.0) (<= t 1.0)) (T t)))
;(rule (=> (<= t 1.0) (T t)))
(rule (=> (and (T t) (L x y z w)
               (or (and (= x1 (+ x 1.0)) (= y1 (+ y 100.0)))
                   (and (or (not (>= x 4.0)) (and (= x1 (+ x 1.0)) (= y1 (+ y 1.0))))
                        (or (not (< x 4.0)) (and (= x1 x) (= y1 y))))
                   (and (or (or  (not (> y (* 10.0 w))) (not (>= z (* 100.0 x))))  (and (= y1 (- 0.0 y)) (= x1 x)))
                        (or (and  (not (<= y (* 10.0 w))) (not (< z (* 100.0 x))))  (and (= y1 y) (= x1 x))))
               )
               (and (= w1 (+ w t)) (= z1 (+ z (* 10.0 t)))))
          (L x1 y1 z1 w1)))
(rule (=> (and (L x y z w) (>= x 4.0) (<= y 2.0)) E))

(query E)
