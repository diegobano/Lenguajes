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

; parse-type : <type> -> Type
; Transforma una lista de elementos de la forma {Num -> Num} o Num en un Type
(define (parse-type s-expr)
  (match s-expr
    ['Num (TNum)]
    [(list arg -> ret) (TFun (parse-type arg) (parse-type ret))]
    [else (error "Parse error")])) 

; parse : expr -> Expr
; Transforma una lista de elementos en una Expr
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

; typeof : Expr -> Type
; Recibe una Expr y retorna sus tipos en formato Type
; Para calcular los tipos ocupa la funcion auxiliar typeof-env ocupando ambientes para definir variables
(define (typeof expr)
  (typeof-env expr empty-env))

; typeof-env : Expr Env -> Type
; Recibe una Expr y el ambiente (Env) en la que esta definida y calcula sus tipos
(define (typeof-env expr env)
  (match expr
    [(num n) (TNum)]
    [(id x) (env-lookup x env)]
    [(add l r) (if (not (equal? (TNum) (typeof l)))
                   (error (string-append "Type error in expression + position 1: expected Num found " (symbol-to-str (parse-msg (typeof l)))))
                   (if (not (equal? (TNum) (typeof r)))
                       (error (string-append "Type error in expression + position 2: expected Num found " (symbol-to-str (parse-msg (typeof r)))))
                       (TNum)))]
    [(fun id targ body tbody) (if (not tbody)
                                  (TFun (TNum) (typeof-env body (env-extend id targ env)))
                                  (let ((etype (typeof-env body (env-extend id targ env))))
                                    (if (equal? tbody etype)
                                        (TFun (TNum) (TNum))
                                        (let ((emsg1 (symbol-to-str (parse-msg etype))) (emsg2 (symbol-to-str (parse-msg tbody))))
                                          (error (string-append "Type error in expression fun position 1: expected " emsg2 " found " emsg1))))))]
                                  
    [(app fun-id arg-expr) (let ((fun-types (typeof-env fun-id env)))
                             (if (equal? fun-types TNum)
                                 (let ((emsg (symbol-to-str (parse-msg fun-types))))
                                   (error (string-append "Type error in expression app position 1: expected {Num -> Num} found " emsg)))
                                 (let ((targ (typeof-env arg-expr env)))
                                   (if (not (equal? (TFun-arg fun-types) targ))
                                       (let ((emsg1 (symbol-to-str (parse-msg (TFun-arg fun-types)))) (emsg2 (symbol-to-str (parse-msg targ))))
                                          (error (string-append "Type error in expression app position 2: expected " emsg1 " found " emsg2)))
                                       (TFun-ret fun-types)))))]))

; typecheck : <s-expr> -> <type>
; Recibe una lista de simbolos de la forma <s-expr> y la retorna de la forma <type>
(define (typecheck s-expr)
  (parse-msg (typeof (parse s-expr))))

; parse-msg : Type -> <type>
(define (parse-msg type)
  (match type
    [(TNum) 'Num]
    [(TFun arg ret) (list (parse-msg arg) '-> (parse-msg ret))]))

(define (symbol-to-str msg)
  (match msg
    [(? symbol?) (symbol->string msg)]
    [(list arg '-> ret) (string-append "{" (symbol-to-str arg) " -> " (symbol-to-str ret) "}")]))

(define (typed-compile s-expr) #f)

#|-----------------------------
Environment abstract data type
 
empty-env  :: Env
env-extend :: Sym Val Env -> Env
env-lookup :: Sym Env -> Val
 
representation BNF:
<env> ::= (mtEnv)
        | (aEnv <id> <val> <env>)
|#
(deftype Env
  (mtEnv)
  (aEnv id type env))
 
(def empty-env  (mtEnv))
 
(def env-extend aEnv)
 
(define (env-lookup x env)
  (match env 
    [(mtEnv) (error 'env-lookup "free identifier: ~a" x)]
    [(aEnv id val rest)
     (if (equal? id x)
         val
         (env-lookup x rest))]))