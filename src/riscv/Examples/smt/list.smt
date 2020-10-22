(declare-datatypes (T) ((Lst nil (cons (hd T) (tl Lst) (foo Int)))))

(define-fun test ((l1 (Lst Int)) (l2 (Lst Int))) (Lst Int)
  (match l1 (
    (nil l2)
    ((cons _ t _) (cons 1 t 2)))))

(check-sat)
(get-model)
