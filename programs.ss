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

;; ============================================================================
;; The Second Law of ==
;;
;; If x is fresh, then (== v x) succeeds and associates v with x,
;; unless x occurs in v
;; ----------------------------------------------------------------------------

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


