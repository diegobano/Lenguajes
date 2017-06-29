#lang play

(require "start.rkt")

;this tests should never fail; these are tests for MiniScheme+ 

(test (run '{+ 1 1}) 2)
  
(test (run '{{fun {x y z} {+ x y z}} 1 2 3}) 6)  
  
(test (run '{< 1 2}) #t)
  
(test (run '{local {{define x 1}}
              x}) 1)
  
(test (run '{local {{define x 2}
                    {define y {local {{define x 1}} x}}}
              {+ x x}}) 4)
  
(test (run '{{fun {x y z} {+ x y z}} 1 2 3}) 6)
  
(test (run '{with {{x 1} {y 2} {z 3}} {+ x y z}}) 6)
  
(test (run '{with {} {{fun {} 42}}}) 42)

(test (run '{local {{datatype Nat
                              {Zero}
                              {Succ n}}}
              {Nat? {Zero}}}) #t)

(test (run '{List? {Empty}}) #t)

(test (run '{match {list {+ 1 1} 4 6}
              {case {Cons h r} => h}
              {case _ => 0}}) 2)

(test (run '{match {list 2 {list 4 5} 6}
              {case {list a {list b c} d} => c}}) 5)

(test (run '{list 1 4 6}) '{list 1 4 6})

(test (run '{{fun {x  {lazy y}} x} 1 {/ 1 0}}) 1)

(test/exn (with-handlers ([exn:fail:contract:divide-by-zero? (lambda (exn) (error "/: division by zero"))])
            (run '{{fun {x  y} x} 1 {/ 1 0}})) "by zero")

(test (run '{local {{datatype T 
                              {C {lazy a}}}
                    {define x {C {/ 1 0}}}}
              {T? x}}) #t)

(test/exn (with-handlers ([exn:fail:contract:divide-by-zero? (lambda (exn) (error "/: division by zero"))])
            (run '{local {{datatype T 
                                    {C {lazy a}}}
                          {define x {C {/ 1 0}}}}
                    {match x
                      {case {C a} => a}}})) "by zero")
  
;; datatypes  
(test (run '{local {{datatype List {Empty} {Cons a b}}} {List? {Empty}}}) #t)
  
(test (run '{local {{datatype List {Empty} {Cons a b}}} {Empty? {Empty}}}) #t)
  
(test (run '{local {{datatype List {Empty} {Cons a b}}} {List? {Cons 1 2}}}) #t)
  
(test (run '{local {{datatype List {Empty} {Cons a b}}} {Cons? {Cons 1 2}}}) #t)
  
(test (run '{local {{datatype List {Empty} {Cons a b}}} {Empty? {Cons 1 2}}})
      #f)
  
(test (run '{local {{datatype List {Empty} {Cons a b}}} {Empty? {Empty}}}) #t)
  
(test (run '{local {{datatype List {Empty} {Cons a b}}} {Cons? {Empty}}})
      #f)      
  
;; match
(test (run '{match 1 {case 1 => 2}}) 2)
  
(test (run '{match 2
              {case 1 => 2}
              {case 2 => 3}})             
      3)
  
(test (run '{match #t {case #t => 2}}) 2)
  
(test (run '{match #f
              {case #t => 2}
              {case #f => 3}})             
      3)

(test (run '{local {{datatype Nat
                              {Zero}
                              {Succ n}}
                    {define pred {fun {n} 
                                      {match n
                                        {case {Zero} => {Zero}}
                                        {case {Succ m} => m}}}}}
              {Succ? {pred {Succ {Succ {Zero}}}}}})
      #t)
(test (run '{local {{datatype Nat
                              {Zero}
                              {Succ n}}
                    {define pred {fun {n} 
                                      {match n
                                        {case {Zero} => {Zero}}
                                        {case {Succ m} => m}}}}}
              {Succ? {pred {Succ {Succ {Zero}}}}}}) #t)

(test (parse '{match {list {+ 1 1} 4 6}
                {case {Cons h r} => h}
                {case _ => 0}}) (mtch (app (id 'Cons) (list (prim-app '+ (list (num 1) (num 1))) (app (id 'Cons) (list (num 4) (app (id 'Cons) (list (num 6) (app (id 'Empty) '()))))))) (list (cse (constrP 'Cons (list (idP 'h) (idP 'r))) (id 'h)) (cse (idP '_) (num 0))))
                                )

(test (parse '{match {list 2 {list 4 5} 6}
                {case {list a {list b c} d} => c}}) (mtch
                                                     (app (id 'Cons) (list (num 2) (app (id 'Cons) (list (app (id 'Cons) (list (num 4) (app (id 'Cons) (list (num 5) (app (id 'Empty) '()))))) (app (id 'Cons) (list (num 6) (app (id 'Empty) '())))))))
                                                     (list (cse (constrP 'Cons (list (idP 'a) (constrP 'Cons (list (constrP 'Cons (list (idP 'b) (constrP 'Cons (list (idP 'c) (constrP 'Empty '()))))) (constrP 'Cons (list (idP 'd) (constrP 'Empty '()))))))) (id 'c))))
                                                    )


;tests for extended MiniScheme+ 

(test (run '{local {{datatype Nat 
                              {Zero} 
                              {Succ n}}
                    {define pred {fun {n} 
                                      {match n
                                        {case {Zero} => {Zero}}
                                        {case {Succ m} => m}}}}}
              {pred {Succ {Succ {Zero}}}}}) '{Succ {Zero}})

(test (run `{local
              {,stream-data ,make-stream ,stream-hd ,ones}
              {stream-hd ones}})
      1)

(test (run `{local
              {,stream-data ,make-stream ,stream-hd ,stream-tl ,ones}
              {stream-hd {stream-tl ones}}})
      1)

(test (run
       `{local ,stream-lib
          {local {,ones ,stream-take}
            {stream-take 11 ones}}}) '{list 1 1 1 1 1 1 1 1 1 1 1})

(test (run `{local ,stream-lib
              {local {,stream-zipWith ,fibs}
                {stream-take 10 fibs}}}) '{list 1 1 2 3 5 8 13 21 34 55})

(test (run `{local ,stream-lib
              {local {,ones ,stream-zipWith}
                {stream-take 10
                             {stream-zipWith
                              {fun {n m}
                                   {+ n m}}
                              ones
                              ones}}}})  '{list 2 2 2 2 2 2 2 2 2 2})
;(test 
;(run `{local ,stream-lib
;               {local {,stream-take ,merge-sort ,fibs ,stream-zipWith}
;                 {stream-take 10 {merge-sort fibs fibs}}}})   '{list 1 1 1 1 2 2 3 3 5 5})

