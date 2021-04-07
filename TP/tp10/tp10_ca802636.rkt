; Cours 10 : Types

#lang plait

;;;;;;;;;;;;;;;;;;;;;;;;
; Définition des types ;
;;;;;;;;;;;;;;;;;;;;;;;;

; Représentation des expressions
(define-type Exp
  [numE (n : Number)]
  [idE (s : Symbol)]
  [plusE (l : Exp) (r : Exp)]
  [multE (l : Exp) (r : Exp)]
  [lamE (par : Symbol) (par-type : Type) (body : Exp)]
  [appE (fun : Exp) (arg : Exp)]
  [trueE]
  [falseE]
  [ifE (cnd : Exp) (e1 : Exp) (e2 : Exp)]
  [eqE (e1 : Exp) (e2 : Exp)]
  [pairE (l : Exp) (r : Exp)]
  [fstE (p : Exp)]
  [sndE (p : Exp)]
  [letrecE (s : Symbol ) (t : Type) (arg : Exp) (body : Exp)]
  

  )

; Représentation du type des expressions
(define-type Type
  [numT]
  [boolT]
  [arrowT (par : Type) (res : Type)]  
  [prodT (l : Type) (r : Type)]
  [varT (is : (Boxof (Optionof Type)))])
   
; Représentation des liaisons identificateurs type
(define-type TypeBinding
  [tbind (name : Symbol) (type : Type)])

; Environnement pour les types
(define-type-alias TypeEnv (Listof TypeBinding))

; Représentation des valeurs
(define-type Value
  [numV (n : Number)]
  [closV (arg : Symbol) (body : Exp) (env : Env)]
  [pairV (f : Value) (s : Value)]
  [undefV]

  )

; Représentation des liaisons
(define-type Binding
  [bind (name : Symbol) (val : (Boxof Value))])

; Manipulation de l'environnement
(define-type-alias Env (Listof Binding))
(define mt-env empty)
(define extend-env cons)

;;;;;;;;;;;;;;;;;;;;;;
; Analyse syntaxique ;
;;;;;;;;;;;;;;;;;;;;;;


(define (parse [s : S-Exp]) : Exp
  (cond
    [(s-exp-match? `true s) (trueE)]
    [(s-exp-match? `false s) (falseE)]
    [(s-exp-match? `NUMBER s) (numE (s-exp->number s))]
    [(s-exp-match? `SYMBOL s) (idE (s-exp->symbol s))]
    [(s-exp-match? `{+ ANY ANY} s)
     (let ([sl (s-exp->list s)])
       (plusE (parse (second sl)) (parse (third sl))))]
    [(s-exp-match? `{* ANY ANY} s)
     (let ([sl (s-exp->list s)])
       (multE (parse (second sl)) (parse (third sl))))]
    [(s-exp-match? `{= ANY ANY}s)
     (let ([sl (s-exp->list s) ])
       (eqE (parse (second sl)) (parse (third sl))))]
    [(s-exp-match? `{lambda {[SYMBOL : ANY]} ANY} s)
     (let ([sl (s-exp->list s)])
       (let ([sll (s-exp->list (first (s-exp->list (second sl))))])
         (lamE (s-exp->symbol (first sll))
               (parse-type (third sll))
               (parse (third sl)))))]
    [(s-exp-match? `{if ANY ANY ANY} s)
     (let ([sl (s-exp->list s)])
       (ifE (parse (second sl)) (parse (third sl)) (parse (fourth sl))))]
    [(s-exp-match? `{let {[SYMBOL : ANY ANY]} ANY} s)
     (let ([sl (s-exp->list s)])
       (let ([sll (s-exp->list (first (s-exp->list (second sl))))])
         (appE
          (lamE (s-exp->symbol (first sll))
                (parse-type (third sll))
                (parse (third sl)))
          (parse (fourth sll)))))]
    [(s-exp-match? `{letrec {[SYMBOL : ANY ANY]} ANY}s )
     (let ([sl (s-exp->list s)])
       (let ([sll (s-exp->list (first (s-exp->list (second sl))))])
         (letrecE (s-exp->symbol (first sll)) (parse-type (third sll)) (parse (fourth sll)) (parse (third sl)))))]
    [(s-exp-match? `{pair ANY ANY} s )
     (let ([sl (s-exp->list s)])
       (pairE (parse (second sl)) (parse (third sl))))]
    [(s-exp-match? `{fst ANY} s)
     (let ([sl (s-exp->list s)])
       (fstE (parse (second sl))))]
    [(s-exp-match? `{snd ANY} s)
     (let ([sl (s-exp->list s)])
       (sndE (parse (second sl))))]
    [(s-exp-match? `{ANY ANY} s)
     (let ([sl (s-exp->list s)])
       (appE (parse (first sl)) (parse (second sl))))]
    [else (error 'parse "invalid input")]))

(define (parse-type [s : S-Exp]) : Type
  (cond
    [(s-exp-match? `? s) (varT (box (none)))]
    [(s-exp-match? `num s) (numT)]
    [(s-exp-match? `bool s) (boolT)]
    [(s-exp-match? `(ANY -> ANY) s)
     (let ([sl (s-exp->list s)])
       (arrowT (parse-type (first sl))
               (parse-type (third sl))))]
    [(s-exp-match? `(ANY * ANY) s)
     (let ([sl (s-exp->list s)])
       (prodT (parse-type (first sl)) (parse-type (third sl))))]
    [else (error 'parse "invalid input")]))


; spécialisation de typecheck pour les opérateurs arithmétiques
(define (typecheck-op [l : Exp] [r : Exp] [env : TypeEnv]) : Type
  (begin
    (unify! (typecheck l env) (numT) l)
    (unify! (typecheck r env) (numT) r)
    (numT)))

; unification de deux types
(define (unify! [t1 : Type] [t2 : Type] [e : Exp]) : Void
  (type-case Type t1
    [(varT is1)
     (type-case (Optionof Type) (unbox is1)
       [(some t3) (unify! t3 t2 e)]
       [(none)
        (let ([t3 (resolve t2)])
          (cond
            [(eq? t1 t3) (void)]
            [(occurs t1 t3) (type-error e t1 t3)]
            [else (set-box! is1 (some t3))]))])]
    [else
     (type-case Type t2
       [(varT is2) (unify! t2 t1 e)]
       [(arrowT t3 t4)
        (type-case Type t1
          [(arrowT t5 t6)
           (begin
             (unify! t3 t5 e)
             (unify! t4 t6 e))]
       
          [else (type-error e t1 t2)])]
       [(prodT t3 t4)
        (type-case Type t1
          [(prodT t5 t6)
           (begin
             (unify! t3 t5 e)
             (unify! t4 t6 e))]
       
          [else (type-error e t1 t2)])]
             
       [else
        (if (equal? t1 t2)
            (void)
            (type-error e t1 t2))])]))

; résolution d'une variable (descente dans les alias)
(define (resolve [t : Type]) : Type
  (type-case Type t
    [(varT is)
     (type-case (Optionof Type) (unbox is)
       [(none) t]
       [(some t2) (resolve t2)])]
    [(arrowT t1 t2) (arrowT (resolve t1) (resolve t2))]
    [(prodT t1 t2) (prodT (resolve t1) (resolve t2))]
    [else t]))

; test de l'apparition de la variable t1 dans le type t2
(define (occurs [t1 : Type] [t2 : Type]) : Boolean
  (type-case Type t2
    [(arrowT t3 t4) (or (occurs t1 t3) (occurs t1 t4))]
    [(varT is)
     (or (eq? t1 t2)
         (type-case (Optionof Type) (unbox is)
           [(none) #f]
           [(some t3) (occurs t1 t3)]))]
    [else #f]))


;;;;;;;;;;;;;;;;;;;;;;;;;;
; Vérification des types ;
;;;;;;;;;;;;;;;;;;;;;;;;;;

(define (typecheck [e : Exp] [env : TypeEnv]) : Type
  (type-case Exp e
    [(numE n) (numT)]
    [(idE s) (type-lookup s env)]
    [(plusE l r) (typecheck-op l r env)]
    [(multE l r) (typecheck-op l r env)]
    [(lamE par par-type body)
     (arrowT par-type
             (typecheck body
                        (extend-env (tbind par par-type) env)))]
    [(appE fun arg)
     (let ([t1 (varT (box (none)))]
           [t2 (varT (box (none)))])
       (begin
         (unify! (typecheck fun env) (arrowT t1 t2) fun)
         (unify! (typecheck arg env) t1 arg)
         t2))]
    [(trueE) (boolT) ]
    [(falseE) (boolT)]

    [(ifE cnd e1 e2) (let ([cnd-t (typecheck cnd env)])
                       (begin ( unify! cnd-t (boolT) cnd) (let ((e1-t  (typecheck e1 env)))
                                                            (let ((e2-t(typecheck e2 env)))
                                                              (begin (unify! e2-t e1-t e2) e1-t)))))]
                       

    [(eqE e1 e2)  (let ([e1-T (typecheck e1 env)])
                    (let ([e2-T (typecheck e2 env)])
                      (begin (unify! e1-T (numT) e1)
                             (unify! e2-T e1-T e2)
                             (boolT) )))]
    [(pairE l r ) (let [(t1 (typecheck l env))]
                    (let [(t2 (typecheck r env))]
                      (begin (unify! t1 (varT (box (none))) l )
                             (unify! t2 (varT (box (none))) r ) (prodT (resolve t1) (resolve t2)))))]
    
    [(fstE p) (let ([pp (typecheck p env)])
                (begin (unify! pp (prodT (varT (box (none))) (varT (box (none))) ) p )
                       (prodT-l (resolve pp))))]
                
    [(sndE p)(let ([pp (typecheck p env)])
               (begin (unify! pp (prodT (varT (box (none))) (varT (box (none))) ) p )
                      (prodT-r (resolve pp))))]

     
    [(letrecE s t arg body) (let [(new-env (extend-env (tbind s t) env))]
                              (let [( type-arg ( typecheck arg new-env))]
                                (let [( body-type ( typecheck body new-env ))]
                                  (begin
                                    (unify! type-arg t arg)
                                    body-type))))]
                              
    

    ))



;(let [(new-env (extend-env (tbind s t) env))]
;                             (let [( type-arg ( typecheck arg new-env))]
;                              (let [( body-type ( typecheck body new-env ))]
;                               (begin (display type-arg)
;                                      (cond
;                                             [(arrowT? t) (begin (unify! type-arg ( arrowT-res  t) arg ) (unify! body-type ( arrowT-res  t) body)(display body-type)
;                                                               (if (equal? type-arg t)
;            
;                                                           (if (equal? body-type  ( arrowT-res  t) )
;                                                                    body-type
;                                                                   (error 'typecheck "typecheck"))(error 'typecheck "typecheck")))]
;                                        [else (begin (unify! type-arg   t arg ) (unify! body-type   t body)(display body-type) (if (equal? type-arg t)
;                        
;                                                            (if (equal? body-type   t )
;                                                              body-type
;                                                             (error 'typecheck "typecheck"))(error 'typecheck "typecheck")))]
;                                                       )))))]
;
; Concaténation de chaînes de caractères
(define (cat [strings : (Listof String)]) : String
  (foldr string-append "" strings))

; Message d'erreur
(define (type-error [expr : Exp] [expected-type : Type] [found-type : Type])
  (error 'typecheck (cat (list "expression " (to-string  expr)
                               ", expected type " (to-string expected-type)
                               ", found type " (to-string found-type)))))

; Message d'erreur
(define (type-error-function [expr : Exp] [found-type : Type])
  (error 'typecheck (cat (list "expression " (to-string  expr)
                               ", expected function "
                               ", found type " (to-string found-type)))))

; Message d'erreur
(define (type-error-product [expr : Exp] [found-type : Type])
  (error 'typecheck (cat (list "expression " (to-string  expr)
                               ", expected product "
                               ", found type " (to-string found-type)))))

; Recherche d'un identificateur dans l'environnement
(define (type-lookup [s : Symbol] [env : TypeEnv]) : Type
  (cond
    [(empty? env) (error 'typecheck "free identifier")]
    [(equal? s (tbind-name (first env))) (tbind-type (first env))]
    [else (type-lookup s (rest env))]))

;;;;;;;;;;;;;;;;;;
; Interprétation ;
;;;;;;;;;;;;;;;;;;

; Interpréteur
(define (interp [e : Exp] [env : Env]) : Value
  (type-case Exp e
    [(numE n) (numV n)]
    [(idE s) (lookup s env)]
    [(plusE l r) (num+ (interp l env) (interp r env))]
    [(multE l r) (num* (interp l env) (interp r env))]
    [(lamE par par-type body) (closV par body env)]
    [(appE f arg)
     (type-case Value (interp f env)
       [(closV par body c-env)
        (interp body (extend-env (bind par (box (interp arg env))) c-env))]
       [else (error 'interp "not a function")])]
    [(ifE cnd e1 e2 )(type-case Value (interp cnd env)
                       [(numV n) (if (not (= n 0)) (interp e1 env) (interp e2 env))]
                       [else (error 'interp "not a number")])]
    [(trueE) (numV 1)]
    [(falseE) (numV 0)]
    [(eqE e1 e2 ) (let ([e1-V (interp e1 env )])
                    (let ([e2-V (interp e2 env)])
                      (if (equal? e1-V e2-V ) (numV 1 ) (numV 0))))]
    [(pairE l r) (pairV (interp l env ) (interp r env ))]
    [(fstE p)
     (let ([pp (interp p env)])
       (if (pairV? pp)
           (pairV-f  pp)
           (error 'interp "not a pair")))]
    [(sndE p)
     (let ([pp (interp p env)])
       (if (pairV? pp)
           (pairV-s  pp)
           (error 'interp "not a pair")))]

    [(letrecE s t arg body)
     (let ([b (box (undefV))])
       (let ([new-env (extend-env (bind s  b) env)])
         (begin
           (set-box! b (interp arg new-env))
           (interp body new-env))))]


    ))

; Recherche d'un identificateur dans l'environnement
(define (lookup [s : Symbol]
                [env : Env]) : Value
  (cond
    [(empty? env) (error 'lookup "free identifier")]
    [(equal? s (bind-name (first env))) (unbox (bind-val (first env)))]
    [else (lookup s (rest env))]))

; Vérification des types pour les opérations arithmétiques
(define (num-op [op : (Number Number -> Number)]
                [l : Value] [r : Value]) : Value
  (if (and (numV? l) (numV? r))
      (numV (op (numV-n l) (numV-n r)))
      (error 'interp "not a number")))

; Spécialisation de num-op pour l'addition
(define (num+ [l : Value] [r : Value]) : Value
  (num-op + l r))

; Spécialisation de num-op pour la multiplication
(define (num* [l : Value] [r : Value]) : Value
  (num-op * l r))

;;;;;;;;;
; Tests ;
;;;;;;;;;


(define (interp-expr [e : S-Exp]) : Value
  (let ([expr (parse e)])
    (begin
      (typecheck expr mt-env)
      (interp expr mt-env))))

(define ( typecheck-expr [e : S-Exp ]) : Type
  ( resolve ( typecheck ( parse e) mt-env )))

( test ( typecheck-expr
         `{ letrec {[fib : ?
                         { lambda {[n : ?]}
                            { if {= n 0}
                                 0
                                 { if {= n 1}
                                      1
                                      {+ { fib {+ n -2} }
                                         { fib {+ n -1} } } } } }]}
             { fib 6} })
       ( numT ))


( test ( typecheck-expr `{ if {= 1 2} true false })
       ( boolT ))


( test/exn ( typecheck-expr `{ if 1 2 3})
           "typecheck")

( test/exn ( typecheck-expr `{= 1 {= 3 2}})
           "typecheck")
( test ( typecheck-expr `{ pair 1 true }) ( prodT ( numT ) ( boolT )))
( test ( typecheck-expr `{ fst { pair 1 true } }) ( numT ))
( test ( typecheck-expr `{ snd { pair 1 true } }) ( boolT ))
( test ( typecheck-expr `{ lambda {[x : (num * bool )]} { fst x} })
       ( arrowT ( prodT ( numT ) ( boolT )) ( numT )))
(parse `{ lambda {[x : (num * bool )]} { fst x}})
( test ( typecheck-expr `{ lambda {[x : (num * num )]} {  if true true false} })
       ( arrowT ( prodT ( numT ) ( numT )) ( boolT )))
(parse `{letrec {[x : num x]} x})
(test/exn (typecheck-expr `{let {[f : (num -> num) {lambda {[x : num]} {f x}}]} 0}) "typecheck")
(test (typecheck-expr `{letrec {[f : (num -> num) {lambda {[x : num]} {f x}}]} 0}) (numT))


(parse `{letrec {[x : (num -> num) x]} x})
(test (typecheck-expr
       `{letrec {[fib : (num -> num)
                      {lambda {[n : num]} {if {= n 0}
                                              0
                                              {if {= n 1} 1
                                                  {+{fib {+ n -2}}
                                                    {fib {+ n -1}}}}}}]}
          {fib 6}}) (numT))
( test ( typecheck-expr `{ let {[f : ? { lambda {[x : ?]} x}]}
                            { let {[x : ? {f 1}]}
                               f} })
       ( arrowT ( numT ) ( numT )))
( test ( typecheck-expr
         `{ letrec {[fib : ?
                         { lambda {[n : ?]}
                            { if {= n 0}
                                 0
                                 { if {= n 1}
                                      1
                                      {+ { fib {+ n -2} }
                                         { fib {+ n -1} } } } } }]}
             { fib 6} })
       ( numT ))


(test (typecheck-expr `{let {[apply-fun : (bool -> (num -> num))
                                        {lambda {[x : bool]}
                                          {if x
                                              {lambda {[x : num]} {+ x 1}}
                                              {lambda {[x : num]} {* x 2}}}}]}
                         {{apply-fun true} 3}})
      (numT))


(test (typecheck-expr `{lambda {[p : ?]} {if {fst p} {snd p} {+ 1 {snd p}}}})
      (arrowT (prodT (boolT) (numT)) (numT)))

( test/exn ( typecheck-expr `{ if true 2 false})
           "typecheck")

( test/exn ( typecheck-expr `{ fst 2 })
           "typecheck")

( test/exn ( typecheck-expr `{ snd 5 })
           "typecheck")

( test ( interp-expr
         `{ letrec {[fib : (num -> num)
                         { lambda {[n : num]}
                            { if {= n 0}
                                 0
                                 { if {= n 1}
                                      1
                                      {+ { fib {+ n -2} }
                                         { fib {+ n -1} } } } } }]}
             { fib 20} })
       (numV 6765))



 

(test (typecheck-expr `{lambda {[p : ?]} {if {fst p} {snd p} {+ 1 {snd p}}}})
      (arrowT (prodT (boolT) (numT)) (numT)))




(test (interp-expr `{let {[f : ?
                             {lambda {[p : ?]} {if {fst p} {snd p} {+ 1 {snd p}}}}]}
                      {f {pair false 3}}})
      (numV 4))

( test/exn ( interp-expr `{= true false})
           "typecheck")
( test/exn ( typecheck-expr `{= 1 false})
           "typecheck")
(test (interp-expr `{ = 1  1 } ) (numV 1))
( test/exn ( interp-expr `{ snd 5 })
           "typecheck")


( test ( interp-expr `{ if {= 1 2} true false })
       (numV 0))
( test/exn ( interp-expr `{ if 1 2 3})
           "typecheck")
( test ( interp-expr `{ pair 1 true }) (pairV (numV 1) (numV 1)))
( test ( interp-expr `{ fst { pair 1 true } }) (numV 1))
( test ( interp-expr `{ snd { pair 1 true } }) (numV 1))
( test ( typecheck-expr `{ lambda {[x : (num * bool )]} { fst x} })
       ( arrowT ( prodT ( numT ) ( boolT )) ( numT )))
( test ( interp-expr
         `{ letrec {[fib : (num -> num)
                         { lambda {[n : num]}
                            { if {= n 0}
                                 0
                                 { if {= n 1}
                                      1
                                      {+ { fib {+ n -2} }
                                         { fib {+ n -1} } } } } }]}
             { fib 6} })
       (numV 8))
(test/exn (interp-expr `{let {[f : (num -> num) {lambda {[x : num]} {f x}}]} 0}) "typecheck")
(test (interp-expr `{letrec {[f : (num -> num) {lambda {[x : num]} {f x}}]} 0}) (numV 0))
( test ( typecheck-expr `{ let {[f : ? { lambda {[x : ?]} x}]}
                            { let {[x : ? {f 1}]}
                               f} })
       ( arrowT ( numT ) ( numT )))

( test ( interp-expr
         `{ letrec {[fib : ?
                         { lambda {[n : ?]}
                            { if {= n 0}
                                 0
                                 { if {= n 1}
                                      1
                                      {+ { fib {+ n -2} }
                                         { fib {+ n -1} } } } } }]}
             { fib 6} })
       (numV 8))
(test (typecheck-expr `{lambda {[x : ?]} {if x 1 2}}) (arrowT (boolT) (numT)))
(test (interp-expr `{let {[apply-fun : (bool -> (num -> num))
                                        {lambda {[x : bool]}
                                          {if x
                                              {lambda {[x : num]} {+ x 1}}
                                              {lambda {[x : num]} {* x 2}}}}]}
                         {{apply-fun true} 3}})
      (numV 4))
(test (typecheck-expr `{lambda {[x : ?]} {if x x false}}) (arrowT (boolT) (boolT)))
(test (typecheck-expr `{lambda {[p : ?]} {if {fst p} {snd p} {+ 1 {snd p}}}})
      (arrowT (prodT (boolT) (numT)) (numT)))
( test ( interp-expr
         `{ letrec {[fib : (num -> num)
                         { lambda {[n : num]}
                            { if {= n 0}
                                 0
                                 { if {= n 1}
                                      1
                                      {+ { fib {+ n -2} }
                                         { fib {+ n -1} } } } } }]}
             { fib 20} })
       (numV 6765))
( test/exn ( interp-expr `{ fst 2 })
           "typecheck")

( test/exn ( typecheck-expr `{ snd 5 })
           "typecheck")
( test/exn ( interp-expr `{= 1 {= 3 2}})
           "typecheck")
( test/exn ( interp-expr `{= 1 false})
           "typecheck")
( test/exn ( interp-expr `{= true false})
           "typecheck")

(test (interp-expr `{let {[f : ?
                             {lambda {[p : ?]} {if {fst p} {snd p} {+ 1 {snd p}}}}]}
                      {f {pair false 3}}})
      (numV 4))