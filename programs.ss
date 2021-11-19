;; load code for The Reasoned Schemer 2nd ed

(load "trs2-impl.scm")
(load "trs2-arith.scm")

;; goals succeed, fail, or have no value. #s always succeeds and #f
;; always fails.  #s is written as succeed and #u as fail

(run* q
      fail)
;; => () because fail obviously fails

(run* q
      (== 'pea 'pod))
;; => () because (== 'pea 'pod) fails.

(run* q
      (== q 'pea))
;; => (pea) because (== q 'pea) succeeds associating q with pea, where
;; q is a fresh variable. If g succeeds, then (run* q g) returns a
;; non-empty list of values associated with q (when g succeeds)

(run* q
      (== 'pea q))
;; => (pea) because the order does not matter

;; ============================================================================
;; The First Law of ==
;;
;; (== u v) can be replaced by (== v u)
;; ----------------------------------------------------------------------------

(run* q
      (== 'pea q))
;; => (pea) We say that the value associated with q is pea. Note that
;; q starts fresh but does not remain fresh because the value
;; pea is associated with it.

(run* q succeed)
;; => (_0) Here the variable q stays fresh; it is reified

;; ============================================================================
;;
;; Every variable is inititally fresh. A variable is no longer fresh
;; if it becomes associated with a no-variable value or if it becomes
;; associated with a a variable that, itself, is no longer fresh
;; ----------------------------------------------------------------------------

(run* q
      (== 'pea 'pea))
;; => (_0) The fresh variable q is reified

(run* q
      (== q q))
;; => (_0) since the (successful) goal (== q q) does not assign any
;; particular value to q.

(run* q
      (fresh (x)
             (== 'pea q)))
;; => (pea) q is associated with pea; x remains fresh. Notice that q
;; starts fresh but then it is associated with the value pea.

(run* q
      (fresh (x)
             (== 'pea x)))
;; => (_0) since q remains fresh and no values are associated with it
;; by the goal (== 'pea x)

(run* q
      (fresh (x)
             (== (cons x '()) q)))
;; => ((_0)) because x stays fresh and the goal wraps x in a list

(run* q
      (fresh (x)
             (== `(,x) q)))
;; => ((_0)) because `(,x) is equivalent to (cons x '()). The backtick
;; operator behaves like a regular quote unless it encounters a
;; variable preceded by a comma, in which case it inserts the value of
;; the variable into the structure.

(run* q
      (fresh (x)
             (== x q)))
;; => (_0) because q stays fresh since x is fresh. We say that x and q
;; are fused when the goal (== x q) succeeds for two fresh variables x
;; and q. Note that the goal succeeds if x and q are fresh. Fused
;; variables get the same association if a value is associated with
;; either variable, including another variable.

(run* q
      (== '(((pea)) pod) '(((pea)) pod)))
;; => (_0) because q remains fresh.

(run* q
      (== '(((pea)) pod) `(((pea)) ,q)))
;; => (pod) because the goal succeeds when q is associated with the
;; value pod

(run* q
      (== `(((,q)) pod) '(((pea)) pod)))
;; => (pea) because the goal succeeds when q is associates with pea

(run* q
      (fresh (x)
             (== `(((,q)) pod) `(((,x)) pod))))
;; => (_0) because q remains fresh even as x and q are fused

(run* q
      (fresh (x)
             (== `(((,q)) ,x) `(((,x)) pod))))
;; => (pod) because x is associated with pod and q is fused with x

(run* q
      (fresh (x)
             (== `(,x ,x) q)))
;; => ((_0 _0)) because q is associated with a list with x as its two
;; elements and x remains fresh.

(run* q
      (fresh (x)
             (fresh (y)
                    (== `(,q ,y) `((,x ,y) ,x)))))
;; => ((_0 _0)) because y and x are fused and then q is associated
;; with the list consisting of x and y but both remain fresh and have the
;; same reified value

(run* q
      (fresh (x)
             (fresh (y)
                    (== `(,x ,y) q))))
;; => ((_0 _1)) because x and y remain fresh and q is associated with
;; the list consisting of x and y

(run* q
      (fresh (x y)
             (== `(,x ,y ,x) q)))
;; => ((_0 _1 _0)) for similar reasons as above.

;; A variable x occurs in a variable y when x (or any variable fused
;; with x) appears in the value associated with y. A variable x occurs
;; in a list l when x (or any variable fused with x) is an element of
;; l, or when x occurs in an element of l.

;; ;; ============================================================================
;; ;; The Second Law of ==
;; ;;
;; ;; If x is fresh, then (== v x) succeeds and associates v with x,
;; ;; unless x occurs in v
;; ;; ----------------------------------------------------------------------------

(run* q
      (conj2 succeed succeed))
;; => (_0) because both goals succeed and q remains fresh

(run* q
      (conj2 succeed (== 'corn q)))
;; => (corn) because (== 'corn q) succeeds when q is bound to q and both goals
;; succeed.

(run* q
      (conj2 fail (== 'corn q)))
;; => () because conj2 succeeds only when both goals succeed but the
;; first goal fails

(run* q
      (conj2 (== 'corn q) (== 'meal q)))
;; => () since the first goal associates q with corn but then the second goal
;; cannot succeed because q is no longer fresh and thus cannot be associated
;; with meal


(run* q
      (conj2 (== 'corn q) (== 'corn q)))
;; => (corn) because the first goal succeeds because q is fresh and thus can
;; be associated with corn. But the second goal succeeds because q is associated
;; with corn (even though it is not fresh)

(run* q
      (disj2 fail fail))
;; => () because disj2 fails if both of its goals fail

(run* q
      (disj2 (== 'olive q) fail))
;; => (olive) because the first goal succeeds since q is fresh and can
;; be associated with olive. disj2 succeeds if either goal succeeds

(run* q
      (disj2 fail (== 'olive q)))
;; => (olive) for the same reason as above. The order of the goals
;; does not matter.

(run* q
      (disj2 (== 'olive q) (== 'oil q)))
;; => (olive oil) since both goals succeed, first when q is associated
;; with olive, and then when q is assoicated with oil. Put it another
;; way: q is associated with oil when the first goal succeeds (and the
;; second goal fails). Likewise, q is associated with oil when the
;; second goal succeeds (and the first goal fails).  Thus, each goal
;; contributes a value to the resulting list.

(run* q
      (fresh (x)
             (fresh (y)
                    (disj2 (== `(,x ,y) q) (== `(,y ,x) q)))))
;; => ((_0 _1) (_0 _1)) both values stay fresh. The first value corresponds to
;; x being reified as _0 and y as _1; the second value corresponds to y being
;; reified as _0 and x as _1

(run* q
      (disj2 (== 'olive q) (== 'oil q)))
;; => (olive oil) and

(run* q
      (disj2 (== 'oil q) (== 'olive q)))
;; => (oil olive) but these results are the same since the order of the values
;; does not matter as these are the values that q can take.

(run* x
      (disj2
       (conj2 (== 'olive x) fail)
       (== 'oil x)))
;; => (oil) because the first goal of conj2 succeeds when q is
;; associated with olive but then the second goal fails, hence conj2
;; fails. The next goal succeeds when x is associated with oil.

(run* x
      (disj2
       (conj2 (== 'olive x) succeed)
       (== 'oil x)))
;; => (olive oil) because this time the conj2 goal succeeds with x
;; bound to olive and the second goal succeeds with x bound to oil,
;; hence both goals contribute to the result.
(run* x
      (disj2
       (== 'oil x)
       (conj2 (== 'olive x) succeed)))
;; => (oil olive) because the order of the goals given to disj2 does
;; not matter.

(run* x
      (disj2
       (conj2 (== 'virgin x) fail)
       (disj2
        (== 'olive x)
        (disj2
         succeed
         (== 'oil x)))))
;; => (olive _0 oil) because the conj2 fails, so we only need to look
;; at disj2: the first goal succeeds when x is bound to olive and the
;; second goal (the second disj2) succeeds with its first goal and x
;; still fresh, and with x bound to oil.

(run* r
      (fresh (x)
             (fresh (y)
                    (conj2
                     (== 'split x)
                     (conj2
                      (== 'pea y)
                      (== `(,x ,y) r))))))
;; => ((split pea)) because the nexted conj2 require all goals to
;; succeed and this happens when x is assoicated with split and y with
;; pea. The last goal associates (split pea) with r.

(run* r
      (fresh (x)
             (fresh (y)
                    (conj2
                     (conj2
                      (== 'split x)
                      (== 'pea y))
                     (== `(,x ,y) r)))))
;; => ((split pea))

(run* r
     (fresh (x y)
            (conj2
             (conj2
              (== 'split x)
              (== 'pea y))
             (== `(,x ,y) r))))
;; =>  ((split pea))

(run* (r x y)
      (conj2
       (conj2
        (== 'split x)
        (== 'pea y))
       (== `(,x ,y) r)))
;; => (((split pea) split pea))

(run* (x y)
      (conj2
       (== 'split x)
       (== 'pea y)))
;; => ((split pea))

(run* (x y)
      (disj2
       (conj2 (== 'split x) (== 'pea y))
       (conj2 (== 'red x) (== 'bean y))))
;; => ((split pea) (red bean))

(run* r
      (fresh (x y)
             (conj2
              (disj2
               (conj2 (== 'split x) (== 'pea y))
               (conj2 (== 'read x) (== 'bean y)))
              (== `(,x ,y soup) r))))
;; => ((split pea soup) (read bean soup))

(run* r
      (fresh (x y)
             (disj2
              (conj2 (== 'split x) (== 'pea y))
              (conj2 (== 'read x) (== 'bean y)))
             (== `(,x ,y soup) r)))
;; => ((split pea soup) (read bean soup))

(run* (x y z)
      (conj2
       (disj2
        (conj2 (== 'split x) (== 'pea y))
        (conj2 (== 'red x) (== 'bean y)))
       (== 'soup z)))
;; ((split pea soup) (red bean soup))

(run* (x y z)
      (disj2
       (conj2 (== 'split x) (== 'pea y))
       (conj2 (== 'red x) (== 'bean y)))
      (== 'soup z))
;; => ((split pea soup) (red bean soup))

(run* (x y)
      (== 'split x)
      (== 'pea y))
;; => ((split pea))

(defrel (teacupo t)
  (disj2 (== 'tea t) (== 'cup t)))

(run* x
      (teacupo x))
;; => (tea cup)

(run* (x y)
      (disj2
       (conj2 (teacupo x) (== #t y))
       (conj2 (== #f x) (== #t y))))
;; => ((#f #t) (tea #t) (cup #t)) because the first value comes from
;; the second conj2 and the last two values come from x taking on the
;; values of tea and cup while y is associated with #t

(run* (x y)
      (teacupo x)
      (teacupo y))
;; => ((tea tea) (tea cup) (cup tea) (cup cup)) because each of x and
;; y is bound to tea and cup, so the run* produces all the possible
;; combinations of these values

(run* (x y)
      (teacupo x)
      (teacupo x))
;; => ((tea _0) (cup _0)) because the first goal associates x with tea
;; and then with cup. The second goal succeeds because x has the
;; needed associations for x so y stays fresh.

(run* (x y)
      (disj2
       (conj2 (teacupo x) (teacupo x))
       (conj2 (== #f x) (teacupo y))))
;; => ((#f tea) (#f cup) (tea _0) (cup _0))

(run* (x y)
      (conde
       ((== 'split x) (== 'pea y))
       ((== 'red x) (== 'bean y))))
;; => ((split pea) (red bean))

(run* x
      (conde
       ((== 'olive x) fail)
       ((== 'oil x))))
;; => (oil)

(run* (x y)
      (conde
       ((fresh (z)
               (== 'lentil z)))
       ((== x y))))
;; => ((_0 _1) (_0 _0)) because in the first goal we have that z is
;; associated with lentil but x and y remain fresh. In the second
;; goal, x remains fresh but y is associated with x so we get (_0 _0)

(run* (x y)
      (conde
       ((== 'split x) (== 'pea y))
       ((== 'red x) (== 'bean y))
       ((== 'green x) (== 'lentil y))))
;; => ((split pea) (red bean) (green lentil))

;; =====================================================================
;; The Law of Conde
;;
;; Every *successful* conde line contributes one or more values
;; ---------------------------------------------------------------------

;; =====================================================================
;; Teaching Old Toys New Tricks
;;
;; ---------------------------------------------------------------------

(run* q
      (caro '(a c o r n) q))
;; => (a)

(run* q
      (caro '(a c o r n) 'a))
;; => (_0) because the goal caro succeeds and q remains fresh

(run* r
      (fresh (x y)
             (caro `(,r ,y) x)
             (== 'pear x)))
;; => (pear) because if the car of a list is pear, then its first element
;; must be pear

;; (defrel (my-caro p a)
;;   (fresh (d)
;;          (== (cons a d) p)))

(run* r
      (fresh (x y)
             (caro '(grape raisin pear) x)
             (caro '((a) (b) (c) y) y)
             (== (cons x y) r)))
;; => ((grape a))

(run* r
      (fresh (v)
             (cdro '(a c o r n) v)
             (fresh (w)
                    (cdro v w)
                    (caro w r))))
;; => (o)

;; (defrel (my-cdro p d)
;;   (fresh (a)
;;          (conso a d p)))

(run* r
 (fresh (x y)
        (cdro '(grape raisin pear) x)
        (caro '((a) (b) (c)) y)
        (== (cons x y) r)))
;; => (((raisin pear) a))

(run* q
      (cdro '(a c o r n) '(c o r n)))
;; => (_0) because the goal succeeds and q remains fresh

(run* x
      (cdro '(c o r n) `(,x r n)))
;; => (o) because the goal succeeds when x is associated with o

(run* l
      (fresh (x)
             (cdro l '(c o r n))
             (caro l x)
             (== 'a x)))
;; => ((a c o r n)) because we know that the first element in the list
;; is associated with x and x is also associated with x. But the cdr of the
;; list is (c o r n), so the list must be (a c o r n)

(run* l
      (conso '(a b c) '(d e) l))
;; => (((a b c) d e))

(run* x
      (conso x '(a b c) '(d a b c)))
;; => (d)

(run* r
      (fresh (x y z)
             (== `(e a d ,x) r)
             (conso y `(a ,z c) r)))
;; => ((e a d c))

(run* x
      (conso x `(a ,x c) `(d a ,x c)))
;; => (d)

(run* l
      (fresh (x)
             (== `(d a ,x c) l)
             (conso x `(a ,x c) l)))
;; => ((d a d c))

(run* l
      (fresh (x)
             (conso x `(a ,x c) l)
             (== `(d a ,x c) l)))
;; => ((d a d c))

;; three definitions of conso
(defrel (my-conso a d p)
  (caro p a)
  (cdro p d))

(defrel (my-conso a d p)
  (== (cons a d) p))

(defrel (my-conso a d p)
  (== `(,a . ,d) p))

(run* l
      (fresh (d t x y w)
             (conso w '(n u s) t)
             (cdro l t)  ; l is (b 0  n u s)
             (caro l x)  ; l is (b . bar)
             (== 'b x)   ; b is x
             (cdro l d)  ; l is (foo o . something)
             (caro d y)  ; d is (o . something)
             (== 'o y))) ; y is o
;; => ((b o n u s))

(run* q
      (nullo '(grape raisin pear)))
;; => ()

(run* q
      (nullo '()))
;; => (_0)

(run* x
      (nullo x))
;; => (())

(defrel (my-nullo x)
  (== '() x))

(run* r
      (fresh (x y)
             (== (cons x (cons y 'salad)) r)))
;; => ((_0 _1 . salad))

(defrel (pairo p)
  (fresh (a d)
         (conso a d p)))

(run* q
      (pairo (cons q q)))
;; => (_0)

(run* x
      (pairo x))
;; => ((_0 . _1))

(run* r
      (pairo (cons r '())))
;; => (_0)

(define (singleton? l)
  (cond
   ((pair? l) (null? (cdr l)))
   (else #f)))

(defrel (singletono l)
  (conde
   ((pairo l) (fresh (d)
                     (cdro l d)
                     (nullo d)))
   (succeed fail)))

(defrel (my-caro p a)
  (fresh (d)
         (conso a d p)))

(defrel (my-cdro p d)
  (fresh (a)
         (conso a d p)))

;; =====================================================================
;; Seeing Old Friends in New Ways
;;
;; ---------------------------------------------------------------------

(defrel (listo l)
  (conde
   ((nullo l) succeed)
   ((pairo l) (fresh (d)
                     (cdro l d)
                     (listo d)))
   (succeed fail)))

(defrel (listo l)
  (conde
   ((nullo l) succeed)
   ((fresh (d)
           (cdro l d)
           (listo d)))))
;; the simplifications are: (cdro l d) succeeds if and only if l is a
;; pair; the last goal fails, so we can remove the whole clause

(defrel (listo l)
  (conde
   ((nullo l))
   ((fresh (d)
           (cdro l d)
           (listo d)))))
;; we can further simplify by getting rid of succeed at the top level
;; of the first clause

;; =====================================================================
;; The Law of #s
;;
;; Any top-level #s can be removed from a conde line
;; ---------------------------------------------------------------------

(run* x
      (listo `(a b ,x d)))
;; => (_0) because x remains fresh: listo succeeds for *any* value of
;; x

(run 1 x
      (listo `(a b c . ,x)))
;; => (()) because when the recursion of listo gets to x (which is
;; fresh) then we have the goal (nullo x) which succeeds with x
;; associated with ().

(run 5 x
     (listo `(a b c . ,x)))
;; => (()
;;     (_0)
;;     (_0 _1)
;;     (_0 _1 _2)
;;     (_0 _1 _2 _3))
;;
;;  because the second line of the conde introduces a fresh variable
;;  which is the cdr of l and then the predicate listo d forces d to be
;;  the empty list, so x, which was a fresh variable, is the car of the list,
;;  i.e., (x). As we move down the recursion stack, we keep on piling on
;;  fresh variables.

(defrel (lolo l)
  (conde
   ((nullo l))
   ((fresh (a)
           (caro l a)
           (listo a))
    (fresh (d)
           (cdro l d)
           (lolo d)))))

(run* q
      (fresh (x y)
             (lolo `((a b) (,x c) (d ,y)))))
;; => (_0) since the lolo goal succeeds for all values of x and y and q
;; remains fresh

(run 1 l
     (lolo l))
;; => (()) because (lolo l) succeeds when l is the empty list

(run 1 q
     (fresh (x)
            (lolo `((a b) . ,x))))
;; => (_0) because lolo succeeds regardless of the value of x, which
;; stays fresh. q stays fresh as well.

(run 1 x
     (lolo `((a b) (c d) . ,x)))
;; => (()) because when the recursion gets to the last term, then
;; nullo succeeds when x is associated with the empty list

(run 5 x
     (lolo `((a b) (c d) . ,x)))
;; => (()
;;     (())
;;     ((_0))
;;     (() ())
;;     ((_0 _1)))

;; a singleton: a proper list with one element
(defrel (singletono l)
  (fresh (a)
         (conso a '() l)))

;; list of singletons
(defrel (loso l)
  (conde
   ((nullo l))
   ((fresh (a)
           (caro l a)
           (singletono a))
    (fresh (d)
           (cdro l d)
           (loso d)))))

(run 1 z
     (loso `((g) . ,z)))
;; => (())

(run 5 x
     (loso x))
;; => (()
;;    ((_0))
;;    ((_0) (_1))
;;    ((_0) (_1) (_2))
;;     ((_0) (_1) (_2) (_3)))
;;
;; The non-empty variables correspond to new fresh variables
;; corresponding to a in the code above

(run 4 r
     (fresh (w x y z)
            (loso `((g) (e . ,w) (,x . ,y) . ,z))
            (== `(,w (,x ,y) ,z) r)))
;; => ((() (_0 ()) ())
;;     (() (_0 ()) ((_1)))
;;     (() (_0 ()) ((_1) (_2)))
;;     (() (_0 ()) ((_1) (_2) (_3))))

(run 3 out
     (fresh (w x y z)
            (== `((g) (e . ,w) (,x . ,y) . ,z) out)
            (loso out)))
;; => (((g) (e) (_0))
;;     ((g) (e) (_0) (_1))
;;     ((g) (e) (_0) (_1) (_2)))

(defrel (membero x l)
  (conde
   ((fresh (a)
           (caro l a)
           (== a x)))
   ((fresh (d)
           (cdro l d)
           (membero x d)))))

;; but we can simplify it
(defrel (membero x l)
  (conde
   ((caro l x))
   ((fresh (d)
           (cdro l d)
           (membero x d)))))

(run* q
      (membero 'olive '(virgin olive oil)))
;; => (_0) because membero succeeds and q remains fresh

(run 1 y
     (membero y '(hummus with pita)))
;; => (hummus)

(run 1 y
     (membero y '(with pita)))
;; => (with)

(run 1 y
     (membero y '(pita)))
;; => (pita)

(run* q
      (membero q '()))
;; => ()

(run* y
      (membero y '(hummus with pita)))
;; => (hummus with pita) so membero is the identity function for a
;; proper list

(run* y
      (membero y '(pear grape . peaches)))
;; => (pear grape) so it is not the identity function for an improper
;; list

(run* x
      (membero 'e `(pasta ,x fagioli)))
;; => (e)

(run 1 x
     (membero 'e `(pasta e ,x fagioli)))
;; => (_0) because the recursion produces e and stops, so x remains
;; fresh

(run 1 x
      (membero 'e `(pasta ,x e fagioli)))
;; => (e)

(run* (x y)
      (membero 'e `(pasta ,x fagioli ,y)))
;; => ((e _0) (_0 e))

(run* q
      (fresh (x y)
             (== `(pasta ,x fagioli ,y) q)
             (membero 'e q)))
;; => ((pasta e fagioli _0) (pasta _0 fagioli e))

(run 1 l
     (membero 'tofu l))
;; => ((tofu . _0))

(run 5 l
     (membero 'tofu l))
;; => ((tofu . _0)
;;     (_0 tofu . _1)
;;     (_0 _1 tofu . _2)
;;     (_0 _1 _2 tofu . _3)
;;     (_0 _1 _2 _3 tofu . _4))

(defrel (proper-membero x l)
  (conde
   ((caro l x)
    (fresh (d)
           (cdro l d)
           (listo d)))
   ((fresh (d)
           (cdro l d)
           (proper-membero x d)))))

(run 12 l
     (proper-membero 'tofu l))
;; ((tofu)
;;  (tofu _0)
;;  (tofu _0 _1)
;;  (_0 tofu)
;;  (tofu _0 _1 _2)
;;  (tofu _0 _1 _2 _3)
;;  (_0 tofu _1)
;;  (tofu _0 _1 _2 _3 _4)
;;  (tofu _0 _1 _2 _3 _4 _5)
;;  (_0 tofu _1 _2)
;;  (tofu _0 _1 _2 _3 _4 _5 _6)
;;  (_0 _1 tofu))

(run 6 x
     (fresh (y z)
            (appendo x y z)))
;; => (()
;;     (_0)
;;     (_0 _1)
;;     (_0 _1 _2)
;;     (_0 _1 _2 _3)
;;     (_0 _1 _2 _3 _4))

(run 6 y
     (fresh (x z)
            (appendo x y z)))
;; => (_0
;;     _0
;;     _0
;;     _0
;;     _0
;;     _0)

(run 6 z
     (fresh (x y)
            (appendo x y z)))
;; => (_0
;;    (_0 . _1)
;;    (_0 _1 . _2)
;;    (_0 _1 _2 . _3)
;;    (_0 _1 _2 _3 . _4)
;;    (_0 _1 _2 _3 _4 . _5))

(run 6 (x y z)
     (appendo x y z))
;; => ((() _0 _0)
;;    ((_0) _1 (_0 . _1))
;;    ((_0 _1) _2 (_0 _1 . _2))
;;    ((_0 _1 _2) _3 (_0 _1 _2 . _3))
;;    ((_0 _1 _2 _3) _4 (_0 _1 _2 _3 . _4))
;;    ((_0 _1 _2 _3 _4) _5 (_0 _1 _2 _3 _4 . _5)))

(run* x
      (appendo '(cake) '(tastes yummy) x))
;; => ((cake tastes yummy))

(run* x
      (fresh (y)
             (appendo `(cake & ice ,y) '(tastes yummy) x)))
;; => ((cake & ice _0 tastes yummy))

(run* x
      (fresh (y)
             (appendo '(cake & ice cream) y x)))
;; => ((cake & ice cream . _0))

(run 1 x
     (fresh (y)
            (appendo `(cake & ice . ,y) '(d t) x)))
;; => ((cake & ice d t))

(run 5 x
     (fresh (y)
            (appendo `(cake & ice . ,y) '(d t) x)))
 ;; => ((cake & ice d t)
 ;;     (cake & ice _0 d t)
 ;;     (cake & ice _0 _1 d t)
 ;;     (cake & ice _0 _1 _2 d t)
 ;;     (cake & ice _0 _1 _2 _3 d t))

(run 5 y
     (fresh (x)
            (appendo `(cake & ice . ,y) '(d t) x)))
;; => (()
;;     (_0)
;;     (_0 _1)
;;     (_0 _1 _2)
;;     (_0 _1 _2 _3))

(run 5 x
     (fresh (y)
            (appendo `(cake & ice . ,y) `(d t . ,y) x)))
;; => ((cake & ice d t)
;;     (cake & ice _0 d t _0)
;;     (cake & ice _0 _1 d t _0 _1)
;;     (cake & ice _0 _1 _2 d t _0 _1 _2)
;;     (cake & ice _0 _1 _2 _3 d t _0 _1 _2 _3))

(run* x
      (fresh (z)
             (appendo '(cake & ice cream) `(d t . ,z) x)))
;; => ((cake & ice cream d t . _0))

(run 6 x
     (fresh (y)
            (appendo x y '(cake & ice d t))))
;; => (()
;;     (cake)
;;     (cake &)
;;     (cake & ice)
;;     (cake & ice d)
;;     (cake & ice d t))

(run 6 y
     (fresh (x)
            (appendo x y '(cake & ice d t))))
;; => ((cake & ice d t)
;;     (& ice d t)
;;     (ice d t)
;;     (d t)
;;     (t)
;;     ())

(run 6 (x y)
     (appendo x y '(cake & ice d t)))
;; => ((() (cake & ice d t))
;;     ((cake) (& ice d t))
;;     ((cake &) (ice d t))
;;     ((cake & ice) (d t))
;;     ((cake & ice d) (t))
;;     ((cake & ice d t) ()))

(run 7 (x y)
     (appendo x y '(cake & ice d t)))
;; same as above because it uses the definition of appendo with the
;; recursive clause at the end.

;; =====================================================================
;; The First Commandment
;;
;; Within each sequence of goals, move non-recursive goals before
;; recursive goals.
;; ---------------------------------------------------------------------

(defrel (swappendo l t out)
  (conde
   ((fresh (a d res)
           (conso a d l)
           (conso a res out)
           (swappendo d t res)))
   ((nullo l) (== t out))))

(run* (x y)
      (swappendo x y '(cake & ice d t)))
;; => ((() (cake & ice d t))
;;     ((cake) (& ice d t))
;;     ((cake &) (ice d t))
;;     ((cake & ice) (d t))
;;     ((cake & ice d) (t))
;;     ((cake & ice d t) ()))

;; =====================================================================
;; The Law of Swapping Conde Lines
;;
;; Swapping two conde lines does not affect the values contributed by
;; conde
;; ---------------------------------------------------------------------

(define (unwrap x)
  (cond
   ((pair? x) (unwrap (car x)))
   (#t x)))

(unwrap '((((pizza)))))
;; => pizza

(unwrap '((((pizza pie) with)) garlic))
;; => pizza

(defrel (unwrapo x out)
  (conde
   ((pairo x) (fresh (a)
                     (caro x a)
                     (unwrapo a out)))
   ((== x out))))

(run* x
      (unwrapo '(((pizza))) x))
;; => ((((pizza)))
;;     ((pizza))
;;     (pizza)
;;     pizza)

(run 1 x
     (unwrapo x 'pizza))
;; => (pizza)

(run 1 x
     (unwrapo `((,x)) 'pizza))
;; => (pizza) because we get to the second clause of the conde while
;; the recursion is going down the first clause

(run 5 x
     (unwrapo x 'pizza))
;; => (pizza
;;     (pizza . _0)
;;     ((pizza . _0) . _1)
;;     (((pizza . _0) . _1) . _2)
;;     ((((pizza . _0) . _1) . _2) . _3))

(run 5 x
     (unwrapo x '((pizza))))
;; => (((pizza))
;;     (((pizza)) . _0)
;;     ((((pizza)) . _0) . _1)
;;     (((((pizza)) . _0) . _1) . _2)
;;     ((((((pizza)) . _0) . _1) . _2) . _3))

(run 5 x
     (unwrapo `((,x)) 'pizza))
;; => (pizza
;;     (pizza . _0)
;;     ((pizza . _0) . _1)
;;     (((pizza . _0) . _1) . _2)
;;     ((((pizza . _0) . _1) . _2) . _3))

;; =====================================================================
;; Members Only
;;
;; ---------------------------------------------------------------------

(defrel (memo x l out)
  (conde
   ((caro l x) (== l out))
   ((fresh (d)
           (cdro l d)
           (memo x d out)))))

(run* q
      (memo 'fig '(pea) '(pea)))
;; => ()

(run* out
      (memo 'fig '(fig) out))
;; => ((fig))

(run* out
      (memo 'fig '(fig pea) out))
;; => ((fig pea))

(run* r
      (memo r '(roll okra fig beet fig pea) '(fig beet fig pea)))
;; => (fig)

(run* x
      (memo 'fig '(fig pea) `(pea ,x)))
;; => ()

(run* x
      (memo 'fig '(fig pea) `(,x pea)))
;; => (fig)

(run* out
      (memo 'fig '(beet fig pea) out))
;; => ((fig pea))

(run 1 out
     (memo 'fig '(fig fig pea) out))
;; => ((fig fig pea))

(run* out
      (memo 'fig '(fig fig pea) out))
;; => ((fig fig pea) (fig pea)) because memo produces all sublists
;; whose first element is fig through its use of recursion

(run* out
      (fresh (x)
             (memo 'fig `(a ,x c fig e) out)))
;; => ((fig c fig e) (fig e))

(run 5 (x y)
     (memo 'fig `(fig d fig e . ,y) x))
;; => (((fig d fig e . _0) _0)
;;     ((fig e . _0) _0)
;;     ((fig . _0) (fig . _0))
;;     ((fig . _0) (_1 fig . _0))
;;     ((fig . _0) (_1 _2 fig . _0)))

;; y remains fresh in the first two values because these correspond to
;; the cases where fig is in the original list--memo succeeds without
;; y being associated with any particular value

;; The other 3 values of y come from the tail of the list: fig must be
;; the car and the cdr remains fresh

(defrel (rembero x l out)
  (conde
   ((nullo l) (== '() out))
   ((conso x out l))
   ((fresh (a d res)
           (conso a d l)
           (conso a res out)
           (rembero x d res)))))

(run* out
      (rembero 'pea '(pea) out))
;; => (() (pea))

(run* out
      (rembero 'pea '(pea pea) out))
;; => ((pea) (pea) (pea pea))

(run* out
      (fresh (y z)
             (rembero y `(a b ,y d ,z e) out)))
;; => ((b a d _0 e)
;;     (a b d _0 e)
;;     (a b d _0 e)
;;     (a b d _0 e)
;;     (a b _0 d e)
;;     (a b e d _0)
;;     (a b _0 d _1 e))

(run* (y z)
      (rembero y `(,y d ,z e) `(,y d e)))
;; => ((d d)
;;     (d d)
;;     (_0 _0)
;;     (e e))

(run 4 (y z w out)
     (rembero y `(,z . ,w) out))
;; ((_0 _0 _1 _1)  y fused with z as _0, w is fused with out as _1
;;                 by the second conde line

;;  (_0 _1 () (_1)) y is _0, z is _1 because it can't be eliminated.
;;                  l is '(_1 w) so (conso a d (_1 w), (conso a res out)
;;                  (rembero _0 d res). d is fresh so it can be () so res
;;                  is also (), so (conso a () out). But d is fused with w,
;;                  so w is (). And a is _1 so out is (_1) since res is ().

;;  (_0 _1 (_0 . _2) (_1 . _2)) y is _0 and z is _1. We called rembero _0
;;                  w res. So (conso _0 res d). But d is fused with w, so
;;                  we have w~(_0 . 2) since res is fresh. But then
;;                  (conso a res out) results in (_1 . _2) since a is _1.

;;  (_0 _1 (_2) (_1 _2))) y is _0 and z is _1. a is also _1. Called
;;                  rembero _0 w res. (conso a' d' w), (cons a' res' res),
;;                  (rembero _0 d' res'). d' is fresh, so d'~() and also
;;                  res'~(). so (conso a' () w), so w~(_2). Now since
;;                  (conso a' res' res), we have (conso _2 () (_2)) so
;;                  res is (_2) but (conso a res out) so out~(_1 _2)

(run 7 (y z w out)
     (rembero y `(,z . ,w) out))
;; => ((_0 _0 _1 _1)
;;     (_0 _1 () (_1))
;;     (_0 _1 (_0 . _2) (_1 . _2))
;;     (_0 _1 (_2) (_1 _2))
;;     (_0 _1 (_2 _0 . _3) (_1 _2 . _3))
;;     (_0 _1 (_2 _3) (_1 _2 _3))
;;     (_0 _1 (_2 _3 _0 . _4) (_1 _2 _3 . _4)))
