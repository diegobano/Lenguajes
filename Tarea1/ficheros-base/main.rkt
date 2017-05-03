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
    [(add l r) (if (not (equal? (TNum) (typeof l)))
                   (error (string-append "Type error in expression + position 1: expected Num found " (parse-msg (typeof l))))
                   (if (not (equal? (TNum) (typeof r)))
                       (error (string-append "Type error in expression + position 2: expected Num found " (parse-msg (typeof r))))
                       (TNum)))]
    [(fun id targ body tbody) (if (not tbody)
                                  (TFun (TNum) (typeof body))
                                  (let ((etype (typeof body)))
                                    (if (equal? tbody etype)
                                        (TFun (TNum) (TNum))
                                        (let ((emsg1 (parse-msg etype)) (emsg2 (parse-msg tbody)))
                                          (error (string-append "Type error in expression fun position 1: expected " emsg2 " found " emsg1))))))]
                                  
    [(app fun-id arg-expr) (let ((fun-types (typeof fun-id)))
                             (if (equal? fun-types TNum)
                                 (let ((emsg (parse-msg fun-types)))
                                   (error (string-append "Type error in expression app position 1: expected {Num -> Num} found " emsg)))
                                 (let ((targ (typeof arg-expr)))
                                   (if (not (equal? (TFun-arg fun-types) targ))
                                       (let ((emsg1 (parse-msg (TFun-arg fun-types))) (emsg2 (parse-msg targ)))
                                          (error (string-append "Type error in expression app position 2: expected " emsg1 " found " emsg2)))
                                       (TFun-ret fun-types)))))]))


(define (typecheck s-expr)
  (string->symbol (parse-msg (typeof (parse s-expr)))))

(define (parse-msg type)
  (match type
    [(TNum) (symbol->string 'Num)]
    [(TFun arg ret) (string-append "{" (parse-msg arg) " -> " (parse-msg ret) "}")]))

(define (typed-compile s-expr) #f)