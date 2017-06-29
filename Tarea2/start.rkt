#lang play
(print-only-errors #t) 
#|
<expr> ::= <num>
         | <bool>
         | <id>
         | <string>
         | {if <expr> <expr> <expr>}
         | {fun {<id>*}}  <expr>}
         | {<expr> <expr>*}
         | {local {<def>*} <expr>}
         | {match <expr> <case>+}

<case> ::= {'case <pattern> '=> <expr>}
<pattern> ::= <num>
         | <bool>
         | <string>
         | <id>
         | <pattern>*

<def>  ::= {define <id> <expr>}
         | {datatype <typename> <type-constructor>*}}


<type-constructor> ::= {<id> <member>*}
<constr-id> :: = <id>
<attr-id> :: = <id>
<typename> :: = <id>
<member>   :: = <id>

|#
; expresiones
(deftype Expr
  (num n)
  (bool b)
  (str s)
  (ifc c t f)
  (id s)
  (app fun-expr arg-expr-list)
  (prim-app name args)   ; aplicación de primitivas
  (fun id body)
  (lcal defs body)
  (mtch val cases))

; definiciones
(deftype Def
  (dfine name val-expr) ; define
  (datatype name variants)) ; datatype

; variantes
(deftype Variant
  (variant name params))

; estructuras de datos
(deftype Struct
  (structV name variant values))

; caso en pattern matching
(deftype Case
  (cse pattern body))

; patrón
(deftype Pattern
  (idP id) ; identificador
  (litP l) ; valor literal 
  (constrP ctr patterns)) ; constructor y sub-patrones

; evaluación lazy
(deftype Lazy
  (lazyE expr env))

;; parse :: s-expr -> Expr
(define(parse s-expr)
  (match s-expr
    [(? number?) (num s-expr)]
    [(? boolean?) (bool s-expr)]
    [(? string?) (str s-expr)]
    [(? symbol?) (id s-expr)]
    [(list 'if c t f) (ifc (parse c) (parse t) (parse f))]
    [(list 'fun xs b) (fun xs (parse b))]
    [(list 'with (list (list x e) ...) b)
     (app (fun x (parse b)) (map parse e))]
    [(list 'local defs body)
     (lcal (map parse-def defs) (parse body))] 
    [(list 'match val-expr cases ...) ; note the elipsis to match n elements
     (mtch (parse val-expr) (map parse-case cases))] ; cases is a list
    [(list 'list a b ...) (app (parse 'Cons) (map parse (list a (append (list 'list) b))))]
    [(list 'list) (parse (list 'Empty))]
    [(list f args ...) ; same here
     (if (assq f *primitives*)
         (prim-app f (map parse args)) ; args is a list
         (app (parse f) (map parse args)))]))

; parse-def :: s-expr -> Def
(define(parse-def s-expr)  
  (match s-expr
    [(list 'define id val-expr) (dfine id (parse val-expr))]
    [(list 'datatype name variants ...) (datatype name (map parse-variant variants))]))

; parse-variant :: sexpr -> Variant
(define(parse-variant v)
  (match v
    [(list name params ...) (variant name params)]))

; parse-case :: sexpr -> Case
(define(parse-case c)
  (match c
    [(list 'case pattern => body) (cse (parse-pattern pattern) (parse body))]))

; parse-pattern :: sexpr -> Pattern
(define(parse-pattern p)  
  (match p
    [(? symbol?)  (idP p)]
    [(? number?)  (litP (num p))]
    [(? boolean?) (litP (bool p))]
    [(? string?)  (litP (str p))]
    [(list 'list) (constrP 'Empty '())]
    [(list ctr patterns ...)
     (if (equal? 'list (first p))
         (constrP 'Cons (map parse-pattern (list (second p) (append (list 'list) (rest (rest p))))))
         (constrP (first p) (map parse-pattern patterns)))]))

;; interp :: Expr Env -> number/procedure/Struct
(define(interp expr env)
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
    ; function (notice the meta interpretation)
    [(fun ids body)
     (λ (arg-vals)
       (interp body (extend-env
                     (map (λ (a) (match a
                                      [(list 'lazy id) id]
                                      [_ a])) ids)
                     (map (λ (a b) (match a
                                      [(list 'lazy id) b]
                                      [_ (match b
                                           [(lazyE exp nEnv) (interp exp nEnv)]
                                           [_ b])])) ids arg-vals) env)))]
    ; application
    [(app fun-expr arg-expr-list)
     ((interp fun-expr env)
      (map (λ (a) (interp-lazy a env)) arg-expr-list))]
    ; primitive application
    [(prim-app prim arg-expr-list)
     (apply (cadr (assq prim *primitives*))
            (map (λ (a) (interp a env)) arg-expr-list))]
    ; local definitions
    [(lcal defs body)
     (def new-env (extend-env '() '() env))
     (for-each (λ (d) (interp-def d new-env)) defs)
     (interp body new-env)]
    ; pattern matching
    [(mtch expr cases)
     (def value-matched (interp expr env))
     (def (cons alist body) (find-first-matching-case value-matched cases))
     (interp body (extend-env (map car alist) (map cdr alist) env))]))

; interp-lazy :: Expr Env -> Lazy
(define (interp-lazy expr env)
  (lazyE expr env))

; interp-def :: Def Env -> Void
(define (interp-def d env)
  (match d
    [(dfine id val-expr)
     (update-env! id (interp val-expr env) env)]
    [(datatype name variants)
     ;; extend environment with new definitions corresponding to the datatype
     (interp-datatype name env)
     (for-each (λ (v) (interp-variant name v env)) variants)]))

; interp-datatype :: String Env -> Void
(define(interp-datatype name env)
  ; datatype predicate, eg. Nat?
  (update-env! (string->symbol (string-append (symbol->string name) "?"))
               (λ (v) (symbol=? (structV-name (interp (lazyE-expr (first v)) (lazyE-env (first v)))) name))
               env))

; interp-variant :: String String Env -> Void
(define (interp-variant name var env)
  ;; name of the variant or dataconstructor
  (def varname (variant-name var))
  ;; variant data constructor, eg. Zero, Succ
  (update-env! varname
               (λ (args)
                 (structV name varname (map
                                        (λ (id val)
                                          (match id
                                            [(list 'lazy s) val]
                                            [_ (def (lazyE value nEnv) val)
                                               (interp value nEnv)]))
                                        (variant-params var)
                                        args)))
               env)
  ;; variant predicate, eg. Zero?, Succ?
  (update-env! (string->symbol (string-append (symbol->string varname) "?"))
               (λ (v) (symbol=? (structV-variant (interp (lazyE-expr (first v)) (lazyE-env (first v)))) varname))
               env))

;;;;
; pattern matcher
(define(find-first-matching-case value cases)
  (match cases
    [(list) #f]
    [(cons (cse pattern body) cs)
     (match (match-pattern-with-value pattern value)
       [#f (find-first-matching-case value cs)]
       [alist (cons alist body)])]))

(define(match-pattern-with-value pattern value)
  (match/values (values pattern value)
                [((idP i) v) (list (cons i v))]
                [((litP (bool v)) b)
                 (if (equal? v b) (list) #f)]
                [((litP (num v)) n)
                 (if (equal? v n) (list) #f)]
                [((constrP ctr patterns) (structV _ ctr-name str-values))
                 (if (symbol=? ctr ctr-name)
                     (apply append (map match-pattern-with-value
                                        patterns str-values))
                     #f)]
                [(x y) (error "Match failure")]))

; Definición de listas en MiniScheme+ con la función length
(def list-def '{{datatype List
                          {Empty}
                          {Cons a b}}
                {define length {fun {l}
                                    {match l
                                      {case {Empty} => {0}}
                                      {case {Cons a b} => {+ 1 {length b}}}}}}})

; Definición de Stream en MiniScheme+
(def stream-data '{datatype Stream
                            {Inf hd {lazy tl}}})

; Definición de make-stream en MiniScheme+
(def make-stream '{define make-stream {fun {hd {lazy tl}}
                                    {Inf hd tl}}})

; Definición de ones en MiniScheme+ para ocupar en ejemplos
(def ones '{define ones {make-stream 1 ones}})

; Definición de stream-hd en MiniScheme+
(def stream-hd '{define stream-hd {fun (x)
                                       (match x
                                         {case {Inf hd tl} => hd})}})

; Definición de stream-tl en MiniScheme+
(def stream-tl '{define stream-tl {fun (x)
                                       (match x
                                         {case {Inf hd tl} => tl})}})

; Definición de stream-take en MiniScheme+
(def stream-take '{define stream-take {fun {n id}
                                           {match n
                                             {case 0 => {Empty}}
                                             {case _ => {Cons {stream-hd id}
                                                              {stream-take {- n 1} {stream-tl id}}}}}}})

; Definición de la stream-lib
(def stream-lib (list stream-data
                      make-stream
                      stream-hd
                      stream-tl
                      stream-take))

; Definición de stream-zipWith
(def stream-zipWith '{define stream-zipWith {fun {f id1 id2}
                                                 {Inf {f
                                                       {stream-hd id1}
                                                       {stream-hd id2}}
                                                      {stream-zipWith f {stream-tl id1} {stream-tl id2}}}}})

; Definición de fibs
(def fibs '{define fibs {make-stream 1
                                     {make-stream 1 {stream-zipWith {fun {n m}
                                                                         {+ n m}}
                                                                    fibs
                                                                    {stream-tl fibs}}}}})

; Definición de merge-sort
(def merge-sort '{define merge-sort {fun {id1 id2} {make-stream {if {> {stream-hd id1} {stream-hd id2}}
                                                                    {stream-hd id2}
                                                                    {stream-hd id1}}
                                                                {merge-sort {if {> {stream-hd id1} {stream-hd id2}}
                                                                                {stream-tl id2}
                                                                                {stream-tl id1}}
                                                                            {if {> {stream-hd id1} {stream-hd id2}}
                                                                                {id1}
                                                                                {id2}}}}}})

;; run :: s-expr -> number
(define(run prog)
  (def parsed-list (map parse-def list-def))
  (def new-env (extend-env '() '() empty-env))
  (for-each (λ (d) (interp-def d new-env)) parsed-list)
  (pretty-printing (interp (parse prog) new-env)))

;; pretty-printing :: Struct -> list/num/bool/str
(define (pretty-printing expr)
  (match expr
    [(structV name variant values)
     (cond
       [(equal? 'List name)
         (append (list 'list) (pretty-printing-list values))]
       [else (append (list variant) (map pretty-printing values))])]
    [_ expr]))

;; pretty-printing-list :: list/Struct -> list/num/bool/str
(define (pretty-printing-list struct)
  (match struct
    [(list a b) (append (list (pretty-printing a)) (pretty-printing-list b))]
    [(structV name variant values)
     (if (equal? 'List name)
         (if (equal? 'Empty variant)
             values
             (pretty-printing-list values))
         (pretty-printing struct))]
    [_ struct]))


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

(define(env-lookup id env)
  (match env
    [(mtEnv) (error 'env-lookup "no binding for identifier: ~a" id)]
    [(aEnv bindings rest)
     (def binding (assoc id bindings))
     (if binding
         ; Se modifica el env-lookup para que,
         ; si encuentra una evaluación lazy, que la evalúe y actualice el ambiente
         (match (cdr binding)
           [(lazyE expr nEnv) (def val (interp expr nEnv))
                              (update-env! id val env)
                              val]
           [_ (cdr binding)])
         (env-lookup id rest))]))

(define (extend-env ids vals env)
  (aEnv (map cons ids vals) ; zip to get list of pairs (id . val)
        env))

;; imperative update of env, adding/overring the binding for id.
(define(update-env! id val env)
  (set-aEnv-bindings! env (cons (cons id val) (aEnv-bindings env))))

;;;;;;;

;;; primitives
; http://pleiad.cl/teaching/primitivas
(define *primitives*
  `((+       ,(lambda args (apply + args)))
    (-       ,(lambda args (apply - args)))
    (*       ,(lambda args (apply * args)))
    (%       ,(lambda args (apply modulo args)))             
    (odd?    ,(lambda args (apply odd? args)))
    (even?   ,(lambda args (apply even? args)))
    (/       ,(lambda args (apply / args)))
    (=       ,(lambda args (apply = args)))
    (<       ,(lambda args (apply < args)))
    (<=      ,(lambda args (apply <= args)))
    (>       ,(lambda args (apply > args)))
    (>=      ,(lambda args (apply >= args)))
    (zero?   ,(lambda args (apply zero? args)))
    (not     ,(lambda args (apply not args)))
    (and     ,(lambda args (apply (lambda (x y) (and x y)) args)))
    (or      ,(lambda args (apply (lambda (x y) (or x y)) args)))))
