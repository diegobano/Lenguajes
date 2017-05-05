#lang play
(require "main.rkt")
(require "machine.rkt")


;; parse-type
(test (parse-type '{Num -> Num})
      (TFun (TNum) (TNum)))
(test/exn (parse-type '{ -> Num}) "Parse error")

(test (parse-type '{{Num -> Num} -> Num})
      (TFun (TFun (TNum) (TNum)) (TNum)))
(test (parse-type 'Num)
      (TNum))
(test (parse-type '{{Num -> Num} -> {Num -> Num}})
      (TFun (TFun (TNum) (TNum)) (TFun (TNum) (TNum))))
(test/exn (parse-type '{Num -> })
          "Parse error")

;; parse
(test (parse '{+ 1 3}) (add (num 1) (num 3)))
(test (parse '{with {x : Num 5} {+ x 3}}) (app (fun 'x (TNum) (add (id 'x) (num 3)) #f) (num 5)))

(test (parse '3) (num 3))
(test (parse 'x) (id 'x))
(test (parse '{fun {x : Num} : Num x})
      (fun 'x (TNum) (id 'x) (TNum)))
(test (parse '{fun {x : {Num -> Num}} x})
      (fun 'x (TFun (TNum) (TNum)) (id 'x) #f))
(test (parse '{{fun {x : Num} : Num {+ x x}} {+ 5 3}})
      (app (fun 'x (TNum) (add (id 'x) (id 'x)) (TNum)) (add (num 5) (num 3))))
(test (parse '{with {x : Num 3} {+ x 5}})
      (app (fun 'x (TNum) (add (id 'x) (num 5)) #f) (num 3)))


;; deBruijn
(test (deBruijn (num 3)) (num 3))
(test (deBruijn (parse '{with {x : Num 5}  {with  {y : Num  {+ x 1}} {+ y x}}}))
      (app (fun-db (app (fun-db (add (acc 0) (acc 1))) (add (acc 0) (num 1)))) (num 5)))
(test/exn (deBruijn (parse 'x)) "Free identifier: x")

;;compile
(test (compile (add (num 2) (num 1))) (list  (INT-CONST 1) (INT-CONST 2) (ADD)))


;;typeof
(test (typeof (parse '{+ 1 3})) (TNum))

(test (typeof (parse '3)) (TNum))
(test (typeof (parse '{fun {x : Num} : Num x}))
      (TFun (TNum) (TNum)))
(test (typeof (parse '{fun {x : {Num -> Num}} x}))
      (TFun (TFun (TNum) (TNum)) (TFun (TNum) (TNum))))
(test (typeof (parse '{{fun {x : Num} : Num {+ x x}} {+ 5 3}}))
      (TNum))
(test (typeof (parse '{with {x : Num 3} {+ x 5}}))
      (TNum))

(test/exn (typeof (parse 'x)) "Type error: No type for identifier x")

(test/exn (typeof (parse '{+ {fun {x : Num} : Num x} 3}))
          "Type error in expression + position 1: expected Num found {Num -> Num}")
(test/exn (typeof (parse '{+ 3 {fun {x : Num} : Num x}}))
          "Type error in expression + position 2: expected Num found {Num -> Num}")
(test/exn (typeof (parse '{{fun {x : Num} : Num x} {fun {x : Num} : Num x}}))
          "Type error in expression app position 2: expected Num found {Num -> Num}")
(test/exn (typeof (parse '{3 3}))
          "Type error in expression app position 1: expected T1 -> T2 found Num")
(test/exn (typeof (parse '{fun {x : Num} : Num {fun {y : Num} {+ x y}}}))
          "Type error in expression fun position 1: expected Num found {Num -> Num}")



;typecheck
(test (typecheck '3) 'Num)