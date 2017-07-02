#lang play

#|
<expr> ::= <num>
         | <bool>
         | <id>
         | <string>
         | {if <expr> <expr> <expr>}
         | {fun {<id>*}}  <expr>}
         | {<expr> <expr>*}
         | {local {<def>*} <expr>}

<def>  ::= {define <id> <expr>}
         | {}


|#
; expresiones
(deftype Expr
  (num n)
  (bool b)
  (str s)
  (ifc c t f)
  (id s)
  (app fun-expr arg-expr-list)
  (prim p) 
  (fun id body)
  (lcal defs body))

; definiciones
(deftype Def
  (dfine name val-expr)
  (defclass id mets)
  (definst class f inst)) ; define

; Clases
(deftype Class
  (class-id id)
  (class cname mets inst deflt-env))

; Instancias
(deftype Instance
  (instance f met-env))

;; parse :: s-expr -> Expr
(define (parse s-expr)
  (match s-expr
    [(? number?) (num s-expr)]
    [(? boolean?) (bool s-expr)]
    [(? string?) (str s-expr)]
    [(? (λ (x)(assq x *primitives*))) (prim (λ (args) (apply (cadr (assq s-expr *primitives*)) args)))]
    [(? symbol?)  (id s-expr)]    
    [(list 'if c t f) (ifc (parse c) (parse t) (parse f))]
    [(list 'fun xs b) (fun xs (parse b))]
    [(list 'with (list (list x e) ...) b)
     (app (fun x (parse b)) (map parse e))]
    [(list 'local defs body)
     (lcal (map parse-def defs) (parse body))] 
    [(list f args ...) (app (parse f) (map parse args))]))

; parse-def :: s-expr -> Def
(define (parse-def s-expr)
  (match s-expr
    ['() '()]
    [(list 'define id val-expr) (dfine id (parse val-expr))]
    [(list 'define-class class mets ...) (defclass class mets)]
    [(list 'define-instance class f defs ...) (definst class (parse f) (parse-def defs))]
    [(list (list met expr) rest ...) (append (list (list (parse met) (parse expr))) (parse-def rest))]))

;; interp :: Expr Env -> number/procedure/Struct
(define (interp expr env)
  (match expr
    ; literals
    [(num n) n]
    [(bool b) b]
    [(str s) s]
    ; conditional
    [(ifc c t f)
     (if (interp c env)
         (interp t env)
         (interp f env))]
    ; identifier
    [(id x) (env-lookup x env)]
    ; function
    [(fun ids body)
     (λ (arg-vals)
       (interp body (extend-env ids arg-vals env)))]
    ; application
    [(app fun-expr arg-expr-list)
     (def interp-args (map (λ (a) (interp a env)) arg-expr-list))
     (def interp-fun (interp fun-expr env))
     (match interp-fun
       [(class-id cname) (def (id met) fun-expr)
                         ((get-method (get-instance cname interp-args env) met) interp-args)]
       [else (interp-fun interp-args)])]
    ;primitive
    [(prim p) p]
    ; local definitions
    [(lcal defs body)
     (def new-env (extend-env '() '() env))
     (for-each (λ (d) (interp-def d new-env)) defs)
     (interp body new-env)]))

; interp-def :: Def Env -> Void
(define (interp-def d env)
  (match d
    [(dfine id val-expr)
     (update-env! id (interp val-expr env) env)]
    [(defclass id mets)
     (def parsed-mets (map parse mets))
     (def defaults (foldl (λ (inst n-env)
                            (extend-env (list (car inst)) (list (interp (cadr inst) env)) n-env))
                          empty-env
                          mets)
       (foldl (λ (d) (interp (filter (λ (d) (not (id? d))) parsed-mets) env))
     (def only-ids (map (λ (d) (match d
                                 [(id name) d]
                                 [(dfine name expr) (id name)]))
                        parsed-mets))
     (update-env! (class-id id) (class id only-ids '() defaults) env)
     (for-each (λ (d)
                 (def (id name) d)
                 (update-env! name (class-id id) env))
               only-ids)]
    [(definst name f mets)
     (update-env! (class-id name)
                  (append-instance (env-lookup (class-id name) env)
                                   (instance (interp f env)
                                             (foldl (λ (inst n-env)
                                                      (extend-env (list (car inst)) (list (interp (cadr inst) env)) n-env))
                                                    empty-env
                                                    mets)))
                  env)]))

;; run :: s-expr -> number
(define (run prog)
  (interp (parse prog) empty-env))

;; append-instance :: Class Instance -> Instance
(define (append-instance cls n-inst)
  (def (class cname mets inst defaults) cls)
  (class cname mets (append (list n-inst) inst defaults)))

;; get-instance :: Expr Expr Env -> Instance
(define (get-instance cname val env)
  (def (class name mets inst defaults) (env-lookup (class-id cname) env))
  (find-instance inst val env))

;; find-instance :: Def Expr -> Def
(define (find-instance insts val env)
  (match insts
    ['() (error "No instance found for value ~a" val)]
    [(list (instance f met-env) rest ...)
     (if (andmap (λ (d) (f (list d))) val)
         (first insts)
         (find-instance rest val env))]))

;; get-method :: Def Expr -> Expr
(define (get-method inst name)
  (def (instance f met-env) inst)
  (env-lookup (id name) met-env))


#|-----------------------------
Environment abstract data type
empty-env   :: Env
env-lookup  :: Sym Env -> Val 
extend-env  :: List[Sym] List[Val] Env -> Env
update-env! :: Sym Val Env -> Void
|#
(deftype Env
  (mtEnv)
  (aEnv bindings rest)) ; bindings is a list of pairs (id . val)

(def empty-env  (mtEnv))

(define (env-lookup id env)
  (match env
    [(mtEnv) (error 'env-lookup "no binding for identifier: ~a" id)]
    [(aEnv bindings rest)
     (def binding (assoc id bindings))
     (if binding
         (cdr binding)
         (env-lookup id rest))]))

(define (extend-env ids vals env)
  (aEnv (map cons ids vals) ; zip to get list of pairs (id . val)
        env))

;; imperative update of env, adding/overring the binding for id.
(define (update-env! id val env)
  (set-aEnv-bindings! env (cons (cons id val) (aEnv-bindings env))))

;;;;;;;

;;; primitives
; http://pleiad.cl/teaching/primitivas
(define *primitives*
  `((+               ,+)
    (-               ,-)
    (*               ,*)
    (%               ,(λ args (apply modulo args)))
    (odd?            odd?)
    (even?           ,even?)
    (/               ,/)
    (=               ,=)
    (<               ,<)
    (<=              ,<=)
    (>               ,>)
    (>=              ,>=)
    (zero?           ,zero?)
    (equal?          ,equal?)
    (number?         ,number?)
    (bool?           ,boolean?)
    (string?         ,string?)
    (not             ,not)
    (and             ,(λ args 
                        (foldl (λ (x y) (and x y))
                               #t args)))
    (or              ,(λ args 
                        (foldl (λ (x y) (or x y))
                               #f args)))
    (string-append   ,string-append)
    (string-length   ,string-length)
    (number->string  ,number->string)
    (string<?        ,string<?)
    ))
