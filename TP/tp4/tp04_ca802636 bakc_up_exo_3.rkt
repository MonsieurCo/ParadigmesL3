; Cours 04 : Les boîtes avec macro simplificatrice

#lang plait

;;;;;;;;;
; Macro ;
;;;;;;;;;

(define-syntax-rule (with [(v-id sto-id) call] body)
  (type-case Result call
    [(v*s v-id sto-id) body]))

;;;;;;;;;;;;;;;;;;;;;;;;
; Définition des types ;
;;;;;;;;;;;;;;;;;;;;;;;;

; Représentation des expressions
(define-type Exp
  [numE (n : Number)]
  [idE (s : Symbol)]
  [plusE (l : Exp) (r : Exp)]
  [multE (l : Exp) (r : Exp)]
  [lamE (par : Symbol) (body : Exp)]
  [appE (fun : Exp) (arg : Exp)]
  [letE (s : Symbol) (rhs : Exp) (body : Exp)]
  [boxE (val : Exp)]
  [unboxE (b : Exp)]
  [setboxE (b : Exp) (val : Exp)]
  [beginE (l : Exp) (r : (Listof Exp))]
  [recordE (fields : (Listof Symbol)) (args : (Listof Exp))]
  [getE (record : Exp) (field : Symbol)])
; Représentation des valeurs
(define-type Value
  [numV (n : Number)]
  [closV (par : Symbol) (body : Exp) (env : Env)]
  [boxV (l : Location)]
  [recV (fields : (Listof Symbol)) (vals : (Listof Value))])

; Représentation du résultat d'une évaluation
(define-type Result
  [v*s (v : Value) (s : Store)])

; Représentation des liaisons
(define-type Binding
  [bind (name : Symbol) (val : Value)])

; Manipulation de l'environnement
(define-type-alias Env (Listof Binding))
(define mt-env empty)
(define extend-env cons)

; Représentation des adresses mémoire
(define-type-alias Location Number)

; Représentation d'un enregistrement
(define-type Storage
  [cell (location : Location) (val : Value)])

; Manipulation de la mémoire
(define-type-alias Store (Listof Storage))
(define mt-store empty)
(define (override-store (c : Storage) (s : Store)): (Listof Storage)
  (if (empty? s) (cons c s) 
      (if (equal? (cell-location (first s)) (cell-location c)) (cons c (rest s)) (cons (first s) (override-store c (rest s))))))

; Recherche un symbole dans une liste de symboles et renvoie la valeur associée
(define (find [fd : Symbol] [fds : (Listof Symbol)] [vs : (Listof Value)]) : Value
  (cond
    [(empty? fds) (error 'interp "no such field")]
    [(equal? fd (first fds)) (first vs)]
    [else (find fd (rest fds) (rest vs))]))




;;;;;;;;;;;;;;;;;;;;;;
; Analyse syntaxique ;
;;;;;;;;;;;;;;;;;;;;;;

(define (parse [s : S-Exp]) : Exp
  (cond
    [(s-exp-match? `NUMBER s) (numE (s-exp->number s))]
    [(s-exp-match? `SYMBOL s) (idE (s-exp->symbol s))]
    [(s-exp-match? `{+ ANY ANY} s)
     (let ([sl (s-exp->list s)])
       (plusE (parse (second sl)) (parse (third sl))))]
    [(s-exp-match? `{* ANY ANY} s)
     (let ([sl (s-exp->list s)])
       (multE (parse (second sl)) (parse (third sl))))]
    [(s-exp-match? `{lambda {SYMBOL} ANY} s)
     (let ([sl (s-exp->list s)])
       (lamE (s-exp->symbol (first (s-exp->list (second sl)))) (parse (third sl))))]
    [(s-exp-match? `{let [{SYMBOL ANY}] ANY} s)
     (let ([sl (s-exp->list s)])
       (let ([subst (s-exp->list (first (s-exp->list (second sl))))])
         (letE (s-exp->symbol (first subst))
               (parse (second subst))
               (parse (third sl)))))]
    [(s-exp-match? `{box ANY} s)
     (let ([sl (s-exp->list s)])
       (boxE (parse (second sl))))]
    [(s-exp-match? `{unbox ANY} s)
     (let ([sl (s-exp->list s)])
       (unboxE (parse (second sl))))]
    [(s-exp-match? `{set-box! ANY ANY} s)
     (let ([sl (s-exp->list s)])
       (setboxE (parse (second sl)) (parse (third sl))))]
    [(s-exp-match? `{begin ANY ANY ...} s)
     (let ([sl (s-exp->list s)])
       (beginE (parse (second sl)) (map parse (rest (rest sl)))))]

   [(s-exp-match? `{record [SYMBOL ANY] ...} s)
     (let ([sl (s-exp->list s)])
       (recordE (map (lambda (l) (s-exp->symbol (first (s-exp->list l)))) (rest sl))
                (map (lambda (l) (parse (second (s-exp->list l)))) (rest sl))))]
    [(s-exp-match? `{get ANY SYMBOL} s)
     (let ([sl (s-exp->list s)])
       (getE (parse (second sl)) (s-exp->symbol (third sl))))]
    [(s-exp-match? `{ANY ANY} s)
     (let ([sl (s-exp->list s)])
       (appE (parse (first sl)) (parse (second sl))))]
    [else (error 'parse "invalid input")]))

;;;;;;;;;;;;;;;;;;
; Interprétation ;
;;;;;;;;;;;;;;;;;;

; Interpréteur
(define (interp [e : Exp] [env : Env] [sto : Store]) : Result
  (type-case Exp e
    [(numE n) (v*s (numV n) sto)]
    [(idE s) (v*s (lookup s env) sto)]
    [(plusE l r)
     (with [(v-l sto-l) (interp l env sto)]
           (with [(v-r sto-r) (interp r env sto-l)]
                 (v*s (num+ v-l v-r) sto-r)))]
    [(multE l r)
     (with [(v-l sto-l) (interp l env sto)]
           (with [(v-r sto-r) (interp r env sto-l)]
                 (v*s (num* v-l v-r) sto-r)))]
    [(lamE par body) (v*s (closV par body env) sto)]
    [(appE f arg)
     (with [(v-f sto-f) (interp f env sto)]
           (type-case Value v-f
             [(closV par body c-env)
              (with [(v-arg sto-arg) (interp arg env sto-f)]
                    (interp body (extend-env (bind par v-arg) c-env) sto-arg))]
             [else (error 'interp "not a function")]))]
    [(letE s rhs body)
     (with [(v-rhs sto-rhs) (interp rhs env sto)]
           (interp body (extend-env (bind s v-rhs) env) sto-rhs))]
    [(boxE val)
     (with [(v-val sto-val) (interp val env sto)]
           (let ([l (new-loc sto-val)])
             (v*s (boxV l) (override-store (cell l v-val) sto-val))))]
    [(unboxE b)
     (with [(v-b sto-b) (interp b env sto)]
           (type-case Value v-b
             [(boxV l) (v*s (fetch l sto-b) sto-b)]
             [else (error 'interp "not a box")]))]
    [(setboxE b val)
     (with [(v-b sto-b) (interp b env sto)]
           (type-case Value v-b
             [(boxV l)
              (with [(v-val sto-val) (interp val env sto-b)]
                    (v*s v-val (override-store (cell l v-val) sto-val)))]
             [else (error 'interp "not a box")]))]
    [(beginE l r)
     (with [(v-l sto-l) (interp l env sto)]
           (if (empty? r ) (v*s v-l sto-l) (aux r env sto-l)))]
    [(recordE fds args)
     (aux-record args fds sto env empty ) ]
      
    [(getE rec fd)
     (type-case Value (v*s-v (interp rec env sto))
       [(recV fds vs) (v*s (find fd fds vs) sto)]
       [else (error 'interp "not a record")])]
   
    ))

(define (aux r-e env sto-l) : Result
  (with [(v sto) (interp (first r-e) env sto-l)]
        (if (empty? (rest r-e)) (v*s v sto) (aux (rest r-e) env sto))))

(define (aux-record args fds sto-l env acc) : Result

  (if (empty? args)
      ( v*s (recV fds acc)  sto-l)
       (with [(v sto) (interp (first args) env sto-l)] 
              (aux-record (rest args) fds sto env (cons v acc)))) )
                                                 


  
;(if (empty? args) 
;   (with [(v sto) (interp (first args) env sto-l)]
;  (if (empty? (rest args)) ()) ( cons v  (aux-record (rest args) sto env)))))


; [(beginE l r)
;     (with [(v-l sto-l) (interp l env sto)]
;           (foldr (lambda (x) (interp x env sto-l)) v-l r))]

; Fonctions utilitaires pour l'arithmétique
(define (num-op [op : (Number Number -> Number)]
                [l : Value] [r : Value]) : Value
  (if (and (numV? l) (numV? r))
      (numV (op (numV-n l) (numV-n r)))
      (error 'interp "not a number")))

(define (num+ [l : Value] [r : Value]) : Value
  (num-op + l r))

(define (num* [l : Value] [r : Value]) : Value
  (num-op * l r))

; Recherche d'un identificateur dans l'environnement
(define (lookup [n : Symbol] [env : Env]) : Value
  (cond
    [(empty? env) (error 'lookup "free identifier")]
    [(equal? n (bind-name (first env))) (bind-val (first env))]
    [else (lookup n (rest env))]))

; Renvoie une adresse mémoire libre
(define (new-loc [sto : Store]) : Location
  (+ (max-address sto) 1))

; Le maximum des adresses mémoires utilisés
(define (max-address [sto : Store]) : Location
  (if (empty? sto)
      0
      (max (cell-location (first sto)) (max-address (rest sto)))))

; Accès à un emplacement mémoire
(define (fetch [l : Location] [sto : Store]) : Value
  (cond
    [(empty? sto) (error 'interp "segmentation fault")]
    [(equal? l (cell-location (first sto))) (cell-val (first sto))]
    [else (fetch l (rest sto))]))

;;;;;;;;;
; Tests ;
;;;;;;;;;

(define (interp-expr [e : S-Exp]) : Value
  (v*s-v (interp (parse e) mt-env mt-store)))

( test ( interp ( parse `{ set-box! { box 2} 3}) mt-env mt-store )
       (v*s ( numV 3) ( list ( cell 1 ( numV 3)))))

( test ( interp-expr `{ let {[b { box 0}]}
                         { begin
                            { set-box! b {+ 1 { unbox b} } }
                            { set-box! b {* 2 { unbox b} } }
                            { set-box! b {+ 3 { unbox b} } } } })
       ( numV 5))


( test ( interp-expr `{ let {[b { box 0}]}
                         { begin
                            { set-box! b {+ 1 { unbox b} } }
                            { set-box! b {* 2 { unbox b} } }
                            { set-box! b {+ 3 { unbox b} } }
                            { set-box! b {+ 9 { unbox b} } }} })
       ( numV 14))
( test ( interp-expr `{ let {[b { box 0}]}
                         { begin
                            { set-box! b {+ 2 { unbox b} } } 
                            { set-box! b {* 2 { unbox b} } }
                            { set-box! b {+ 3 { unbox b} } }
                            { set-box! b {+ 8 { unbox b} } }
                            { set-box! b {* 3 { unbox b} } }}})
       ( numV 45))

(test (interp-expr `{let {[b {box 0}]}
                      {begin
                        {set-box! b {+ 1 {unbox b}}}
                        }})
      (numV 1))



(test (interp (parse `{let {[b { box 0}]}
                        {let {[c {box 1}]}
                          {let {[a {box 2}]}
                            {set-box! b 8}}}}) mt-env mt-store )
      (v*s (numV 8) (list (cell 1 (numV 8)) (cell 2 (numV 1)) (cell 3 (numV 2)))))

(test (interp-expr `{let {[b1 {box 1}]}
                      {let {[b2 {box 2}]}
                        {let {[v {set-box! b1 3}]}
                          {unbox b2}}}})
      (numV 2))

(test (interp-expr `{let {[b1 {box 1}]}
                      {let {[b2 {box 2}]}
                        {let {[v {set-box! b2 3}]}
                          {unbox b1}}}})
      (numV 1))   
