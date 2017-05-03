#lang play
(require "machine.rkt")
(print-only-errors #t) 
;;;;;;;;;;;;;;;;;;;;;;;
;; Language definition
;;;;;;;;;;;;;;;;;;;;;;;

#|
<s-expr> ::= <num>
         | <id>
         | {+ <s-expr> <s-expr>}
         | {with {<s-expr> : <type> <s-expr>} <s-expr>}
         | {fun {<id>  : <s-expr>} [: <type>] <expr>}
         | {<expr> <expr>}
 
<type> ::= Num
         | {<type> -> <type>}}
|#
(deftype Expr
  (num n)
  (add l r)
  (id s) 
  (fun id targ body tbody)
  (fun-db body)
  (acc n) ;Se usa para la pregunta 3
  (app fun-id arg-expr))

(deftype Type
  (TNum)
  (TFun arg ret))

; parse-type : Expr -> Type
(define (parse-type s-expr)
  (match s-expr
    ['Num (TNum)]
    [(list arg -> ret) (TFun (parse-type arg) (parse-type ret))]
    [else (error "Parse error")])) 

(define (parse s-expr)
  (match s-expr
    [(? number?) (num s-expr)]
    [(? symbol?) (id s-expr)]
    [(list '+ l r) (add (parse l) (parse r))]
    [(list 'fun (list id : targ) : tbody body) (fun id (parse-type targ) (parse body) (parse-type tbody))]
    [(list 'fun (list id : targ) body) (fun id (parse-type targ) (parse body) #f)]
    [(list 'with (list id : targ e1) e2) (app (parse (list 'fun (list id : targ) e2)) (parse e1))]
    [(list e1 e2) (app (parse e1) (parse e2))]))

(define (deBruijn expr)#f)

(define (compile expr) #f)

(define (typeof expr)
  (match expr
    [(num n) (TNum)]
    [(id x) (TNum)]
    [(add l r) (if (not (= TNum (typeof l)))
                   (error "Type error in expression + position 1: expected TNum found ~s~n" (typeof l))
                   (if (not (= TNum (typeof r)))
                       (error "Type error in expression add position 2: expected TNum found ~s~n" (typeof r))
                       (TNum)))]
    [(fun id targ body tbody) (if (not tbody)
                                  (TFun (TNum) (typeof body))
                                  (let ((etype (typeof body)))
                                    (match etype
                                      [(tbody) (TFun (TNum) (TNum))]
                                      [else (error "Type error in expression fun position 1: expected ~s found ~a~n" tbody etype)])))]
                                  
    [(app fun-id arg-expr) (let ((fun-types (typeof fun-id)))
                             (if (not (= (first fun-types) TFun))
                                 (error "Type error in expression app position 1: expected TFun found ~s~n" (first fun-types))
                                 (let ((targ (typeof arg-expr)))
                                   (if (not (= (second fun-types) targ))
                                       (error "Type error in expression app position 2: expected ~a found ~s~n" (second fun-types) targ)
                                       (third fun-types)))))]))


(define (typecheck s-expr) #f)

(define (typed-compile s-expr) #f)