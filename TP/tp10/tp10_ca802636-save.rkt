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
  [prodT (l : Type) (r : Type)])
   
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

  )

; Représentation des liaisons
(define-type Binding
  [bind (name : Symbol) (val : Value)])

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

;;;;;;;;;;;;;;;;;;;;;;;;;;
; Vérification des types ;
;;;;;;;;;;;;;;;;;;;;;;;;;;

(define (typecheck [e : Exp] [env : TypeEnv]) : Type
  (type-case Exp e
    [(numE n) (numT)]
    [(idE s) (type-lookup s env)]
    [(plusE l r)
     (let ([t1 (typecheck l env)]
           [t2 (typecheck r env)])
       (type-case Type t1
         [(numT)
          (type-case Type t2
            [(numT) (numT)]
            [else (type-error r (numT) t2)])]
         [else (type-error l (numT) t1)]))]
    [(multE l r)
     (let ([t1 (typecheck l env)]
           [t2 (typecheck r env)])
       (type-case Type t1
         [(numT)
          (type-case Type t2
            [(numT) (numT)]
            [else (type-error r (numT) t2)])]
         [else (type-error l (numT) t1)]))]
    [(lamE par par-type body)
     (arrowT par-type
             (typecheck body
                        (extend-env (tbind par par-type) env)))]
    [(appE fun arg)
     (let ([t1 (typecheck fun env)]
           [t2 (typecheck arg env)])
       (type-case Type t1
         [(arrowT par-type res-type)
          (if (equal? par-type t2)
              res-type
              (type-error arg par-type t2))]
         [else (type-error-function fun t1)]))]
    [(trueE) (boolT) ]
    [(falseE) (boolT)]

    [(ifE cnd e1 e2) (let ([cnd-t (typecheck cnd env)])
                                  (if (equal? cnd-t (boolT)) (begin (typecheck e1 env) (typecheck e2 env))(error 'typecheck "typecheck")))]

     [(eqE e1 e2)  (let ([e1-T (typecheck e1 env)])
                     (let ([e2-T (typecheck e2 env)])
                       (if (equal? e1-T e2-T )(boolT) (error 'typecheck "typecheck"))))]
    [(pairE l r ) (prodT (typecheck l env) (typecheck r env))]
    [(fstE p) (let ([pp (typecheck p env)])
                 (if (prodT? pp ) (prodT-l pp) (type-error-product p pp)))]
                
    [(sndE p)(let ([pp (typecheck p env)])
                 (if (prodT? pp ) (prodT-r pp) (type-error-product p pp)))]

     
    [(letrecE s t arg body) (let [(new-env (extend-env (tbind s t) env))]
                               (let [( type-arg ( typecheck arg new-env))]
                                 (let [( body-type ( typecheck body new-env ))]
                              (if (equal? type-arg t)
                                   
                                  (if (equal? body-type ( arrowT-res  t) )
                                      body-type
                                      (error 'typecheck "typecheck"))
                                  (error 'typecheck "typecheck")))))]
                              
    ;(let [(new-env (extend-env (tbind s t) env))]
     ;                        (let [( l ( typecheck body new-env ))]
      ;                        (let [( ll ( typecheck arg new-env))]
       ;                       (if (equal? l ll) l (error 'typecheck "typecheck")))))]
                
    

    ))

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
        (interp body (extend-env (bind par (interp arg env)) c-env))]
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

    [(letrecE s t arg body) (letrec ([new-env (extend-env (bind s  val) env)]
              [val (interp arg new-env)])
       (interp body new-env))]


    ))

; Recherche d'un identificateur dans l'environnement
(define (lookup [s : Symbol]
                [env : Env]) : Value
  (cond
    [(empty? env) (error 'lookup "free identifier")]
    [(equal? s (bind-name (first env))) (bind-val (first env))]
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

(define (typecheck-expr [e : S-Exp]) : Type
  (typecheck (parse e) mt-env))
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


(parse `{letrec {[x : (num -> num) x]} x})
(test (typecheck-expr
       `{letrec {[fib : (num -> num)
                      {lambda {[n : num]} {if {= n 0}
                                              0
                                              {if {= n 1} 1
                                                  {+{fib {+ n -2}}
                                                    {fib {+ n -1}}}}}}]}
          {fib 6}}) (numT))
(test/exn (typecheck-expr `{let {[f : (num -> num) {lambda {[x : num]} {f x}}]} 0}) "typecheck")
(test (typecheck-expr `{letrec {[f : (num -> num) {lambda {[x : num]} {f x}}]} 0}) (numT))




