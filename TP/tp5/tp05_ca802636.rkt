; Cours 05 : Les variables

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
  [setE (s : Symbol) (val : Exp)]
  [beginE (l : Exp) (r : Exp)]
  [addressE (s : Symbol)]
  [contentE (e : Exp)]
  [set-contentE ( l : Exp) (r : Exp)]
  [mallocE (e : Exp) ]
  [freeE (e : Exp)] 
  )

;verifier si n est un interger
( define ( integer? n) (= n ( floor n)))


; Représentation des valeurs
(define-type Value
  [numV (n : Number)]
  [closV (par : Symbol) (body : Exp) (env : Env)])

; Représentation du résultat d'une évaluation
(define-type Result
  [v*s (v : Value) (s : Store)])

; Représentation des liaisons
(define-type Binding
  [bind (name : Symbol) (location : Location)])

; Manipulation de l'environnement
(define-type-alias Env (Listof Binding))
(define mt-env empty)
(define extend-env cons)

; Représentation des adresses mémoire
(define-type-alias Location Number)

; Représentation d'un enregistrement
(define-type Storage
  [cell (location : Location) (val : Value)])
;représentation d'un pointeur
(define-type  Pointer[pointer (loc : Location) (size : Number)])

; Manipulation de la mémoire
(define-type  Store[store (storages : (Listof  Storage))(pointers : (Listof  Pointer))])
(define mt-store (store empty empty))
(define (override-store [new-cell : Storage]  [old-sto : Store ]) : Store
  (store (cons new-cell (store-storages old-sto)) (store-pointers old-sto) ))

;(define (override-store (c : Storage) (s : Store)): (Listof Storage)
; (if (empty? s) (cons c s) 
;    (if (equal? (cell-location (first s)) (cell-location c)) (cons c (rest s)) (cons (first s) (override-store c (rest s))))))

;(define (override-store [new-cell : Storage]  [old-storages : ( Listof Storage) ] pointers : (Listof  Pointer)]) : Store
; (if (empty? (store-storages old-sto)) (cons new-cell old-sto)
;    (if (equal? (cell-location (first (store-storages old-sto))) (cell-location new-cell))
;       (store (cons new-cell (rest (store-storages old-sto))) (store-pointers old-sto))
;      (override-store new-cell 
;(store (cons new-cell (store-storages old-sto)) (store-pointers old-sto) ))

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
    [(s-exp-match? `{set! SYMBOL ANY} s)
     (let ([sl (s-exp->list s)])
       (setE (s-exp->symbol (second sl)) (parse (third sl))))]
    [(s-exp-match? `{begin ANY ANY} s)
     (let ([sl (s-exp->list s)])
       (beginE (parse (second sl)) (parse (third sl))))]
    [(s-exp-match? `{address SYMBOL} s)
     (let ([sl (s-exp->list s)])
       (addressE (s-exp->symbol (second sl))))]
    [(s-exp-match? `{content ANY} s)
     (let ([sl (s-exp->list s)])
       (contentE (parse (second sl ))))]
    [(s-exp-match? `{set-content! ANY ANY } s)
     (let ([sl (s-exp->list s)])
       (set-contentE (parse (second sl)) (parse (third sl))))]
    [(s-exp-match? `{malloc ANY} s)
     (let ([sl (s-exp->list s)])
       (mallocE (parse (second sl))))]

    [(s-exp-match? `{free ANY} s)
     (let ([sl (s-exp->list s)])
       (freeE (parse (second sl))))]
                   
     
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
    [(idE s) (v*s (fetch (lookup s env) sto) sto)]
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
              (type-case Exp arg
                [(idE s) (interp body
                                 (extend-env (bind par (lookup s env)) c-env)
                                 sto-f)]
                [else (with [(v-arg sto-arg) (interp arg env sto-f)]
                            (let ([l (new-loc sto-arg)])
                              (interp body
                                      (extend-env (bind par l) c-env)
                                      (override-store (cell l v-arg) sto-arg))))])]
             [else (error 'interp "not a function")]))]
    [(letE s rhs body)
     (with [(v-rhs sto-rhs) (interp rhs env sto)]
           (let ([l (new-loc sto-rhs)])
             (interp body
                     (extend-env (bind s l) env)
                     (override-store (cell l v-rhs) sto-rhs))))]
    [(setE var val)
     (let ([l (lookup var env)])
       (with [(v-val sto-val) (interp val env sto)]
             (v*s v-val (override-store (cell l v-val) sto-val))))]
    [(beginE l r)
     (with [(v-l sto-l) (interp l env sto)]
           (interp r env sto-l))]

    [(addressE var) (v*s (numV (lookup var env)) sto) ]
    [(contentE loc) 
     (with [(v-l sto-l) (interp loc env sto)]
           (if (integer? ( numV-n v-l))
               (v*s (fetch ( numV-n v-l) sto-l) sto-l) (error 'interp "segmentation fault")))]
    
    [(set-contentE loc expr) (with [(v-l sto-l) (interp loc env sto)]
                                   (if (integer? ( numV-n v-l))  
                                       (with[(exp-r sto-exp)(interp expr env sto-l)]
                                            (v*s exp-r (override-store (cell ( numV-n v-l) exp-r) sto-exp))) (error 'interp "segmentation fault")) )]



    [(mallocE expr) (with [(v-l sto-l) (interp expr env sto)]
                          (if (and (numV? v-l) (>(numV-n v-l) 0)) 
                              (malopopo (numV-n v-l) sto-l empty (numV-n v-l) ) (error 'interp "not a size")))]
    
    ; [(mallocE expr) (with [(v-l sto-l) (interp expr env sto)]
    ;                      (if (and (numV? v-l) (>(numV-n v-l) 0)) 
    ;                         (with [(v-malloc sto-malloc) (malopopo (numV-n v-l) sto-l empty)]
    ;                              (v*s v-malloc (store  (override-store (cell ( numV-n v-malloc)  v-l) sto-malloc) sto-malloc)) ) (error 'interp "not a size")))]

    [(freeE expr) (with  [(v-l sto-l) (interp expr env sto)]
                         (v*s (numV 0)(store (mega-free v-l (pointer-size (find-pointouille (numV-n v-l) (store-pointers sto-l))) (store-storages sto-l)) (elimine-pointeur (find-pointouille (numV-n v-l) (store-pointers sto-l)) (store-pointers sto-l) ))))]
    
    ))



;(define (mega-free pointeur sto acc)
;(if (empty? (store-storages sto)) (error 'mega-free "segmentation fault")
;          (if (equal? (fetch  (cell-location (first (store-storages sto)))sto ) pointer )
;           (if (equal? 0 acc) (sto) (mega-free pointeur (store (rest (store-storages sto)) (store-pointers sto))))
;           (mega-free pointeur (store (rest (store-storages sto)) (store-pointers sto))))))

(define (mega-free l size sto-storage)
  (cond
    [(empty? sto-storage) empty]
    [(equal? (cell-val (first sto-storage)) l)  ( cons (first sto-storage) (libere  size    (rest sto-storage)))]
    [else ( cons (first sto-storage) (mega-free l size (rest sto-storage)))]
    ))


(define (libere n sto-storage)
  (cond
    [(equal? n 0)  sto-storage]
    [else (libere (- n 1 ) (rest sto-storage))]))


(define (find-pointouille l sto-pointeur) : Pointer
  (cond
    [(empty? sto-pointeur ) (error 'find-pointouille "not an allocated pointer")]
    [(equal? l (pointer-loc (first sto-pointeur))) (first  sto-pointeur)]
    [else (find-pointouille l (rest  sto-pointeur))])) 

(define (elimine-pointeur pointeur p-list) :( Listof Pointer)
  (cond
    [(empty? p-list) empty]
    [(equal? pointeur (first p-list)) (rest p-list)]
    [else ( cons (first p-list) (elimine-pointeur pointeur (rest p-list)))]))


(define (malopopo n sto acc origine )
  (if (= n 0) (v*s (numV (first (reverse acc))) (store (store-storages sto) (cons (pointer (first (reverse acc)) origine )  (store-pointers sto))))
      (let ([l (new-loc sto)])
        (malopopo (- n 1 )  (override-store (cell l (numV 0)) sto) (cons l acc ) origine ))))
      

;(define (is-that-location-a-location-of-a-pointer-from-malloc?-if-so-delete-it [l : Location ] [sto : Store] ) : Store
;(if (empty? (store-pointers sto)) (error 'is-that-location-a-location-of-a-pointer-from-malloc?-if-so-delete-it "not an allocated pointer")
;        (if (equal? (first (store-pointers sto) ) (fetch l))
;            ( mega-free (fetch l) sto (pointer-size (fetch l)))
;          (is-that-location-a-location-of-a-pointer-from-malloc?-if-so-delete-it l (store (store-storages sto) (rest (store-pointers)))))))

;(define (is-that-location-a-location-of-a-pointer-from-malloc?-if-so-delete-it [l : Location ] [sto-l : Listof storages] [sto-p : Listof Pointer] [origin-store : Store]  )  : Store
; ( cond 
; [(empty? sto-l ) (error 'is-that-location-a-location-of-a-pointer-from-malloc?-if-so-delete-it "not an allocated pointer")]
;[(equal? (equal? (first (store-pointers sto) ) (fetch l origin-store)))
;(store (mega-free (fetch l origine-store) sto-l sto-p  (pointer-size (fetch l origin-store))) (elimine-pointeur (fetch l origin-store)sto-p) )]
;[else (
;[(equal? (bind-name (first e)) s) (rest e)]
;[else (cons (first e) (unbind s (rest e)))]))

  
;(if (empty? (store-pointers sto)) (error 'is-that-location-a-location-of-a-pointer-from-malloc?-if-so-delete-it "not an allocated pointer")
;        (if (equal? (first (store-pointers sto) ) (fetch l))
;            ( mega-free (fetch l) sto (pointer-size (fetch l)))
;          (is-that-location-a-location-of-a-pointer-from-malloc?-if-so-delete-it l (store (store-storages sto) (rest (store-pointers)))))))
                                                                                                                                     




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
(define (lookup [n : Symbol] [env : Env]) : Location
  (cond
    [(empty? env) (error 'lookup "free identifier")]
    [(equal? n (bind-name (first env))) (bind-location (first env))]
    [else (lookup n (rest env))]))

; Renvoie une adresse mémoire libre
(define (new-loc [sto : Store]) : Location
  (+ (max-address sto) 1))

; Le maximum des adresses mémoires utilisés
(define (max-address [sto : Store]) : Location
  (if (empty? (store-storages sto) )
      0
      (max (cell-location (first (store-storages sto))) (max-address (store (rest (store-storages sto)) (store-pointers sto)   )))))

; Accès à un emplacement mémoire
(define (fetch [l : Location] [sto : Store]) : Value
  (cond
    [(empty? (store-storages sto)) (error 'interp "segmentation fault")]
    [(equal? l (cell-location (first (store-storages sto)))) (cell-val (first (store-storages sto)))]
    [else (fetch l (store (rest (store-storages sto)) (store-pointers sto)))]))

;;;;;;;;;
; Tests ;
;;;;;;;;;

(define (interp-expr [e : S-Exp]) : Value
  (v*s-v (interp (parse e) mt-env mt-store)))

(test (interp-expr `{let {[x 0]} {address x}}) (numV 1))
(test (interp-expr `{let {[x 0]} {content 1}}) (numV 0))(test (interp-expr `{let {[x 0]}
                                                                              {begin {set-content! 1 2}
                                                                                     x}})
                                                              (numV 2))

(test/exn (interp-expr `{let {[x 0]} {content -4}}) "segmentation fault")





(test (interp (parse `{let{[p{malloc 3}]}p}) mt-env  mt-store)(v*s (numV 1) (store (list (cell 4 (numV 1))(cell 3 (numV 0))(cell 2 (numV 0))(cell 1 (numV 0)))(list (pointer 1 3)))))


(test (interp (parse `{ let {[p { malloc 3}]}
                         {let {[c {malloc 4}]}
                           {let {[a {malloc 5}]}
                             {set-content! 11 2}}}}) mt-env mt-store) (v*s (numV 2) (store
                                                                                     (list (cell 11 (numV 2))
                                                                                           (cell 15 (numV 10))
                                                                                           (cell 14 (numV 0))
                                                                                           (cell 13 (numV 0))
                                                                                           (cell 12 (numV 0))
                                                                                           (cell 11 (numV 0))
                                                                                           (cell 10 (numV 0))
                                                                                           (cell 9 (numV 5))
                                                                                           (cell 8 (numV 0))
                                                                                           (cell 7 (numV 0))
                                                                                           (cell 6 (numV 0))
                                                                                           (cell 5 (numV 0))
                                                                                           (cell 4 (numV 1))
                                                                                           (cell 3 (numV 0))
                                                                                           (cell 2 (numV 0))
                                                                                           (cell 1 (numV 0)))
                                                                                     (list (pointer 10 5) (pointer 5 4) (pointer 1 3)))))





( test/exn (interp-expr `{ let {[p { malloc -3}]} p})
           "not a size")

( test ( interp ( parse `{ let {[p { malloc 3}]} { free p} })
                mt-env
                mt-store )
       (v*s ( numV 0) ( store ( list ( cell 4 ( numV 1)))
                              empty )))

( test ( interp ( parse `{ let {[p { malloc 3}]} p}) mt-env mt-store )
       (v*s ( numV 1) ( store ( list ( cell 4 ( numV 1))
                                     ( cell 3 ( numV 0))
                                     ( cell 2 ( numV 0))
                                     ( cell 1 ( numV 0)))
                              ( list ( pointer 1 3)))))

( test/exn ( interp ( parse `{ let {[p { malloc 3}]}
                                {begin
                                  {free p}
                                  {free p}}})
                    mt-env
                    mt-store )
           "not an allocated pointer")

(test/exn (interp-expr `{let {[a {malloc 8}]}
                          {free z}})
          "free identifier")

(test (interp (parse `{let {[p {malloc 3}]}
                        {let {[c {malloc 4}]}
                          (free p)}}) mt-env mt-store)
      (v*s (numV 0) (store (list (cell 9 (numV 5))
                                 (cell 8 (numV 0))
                                 (cell 7 (numV 0))
                                 (cell 6 (numV 0))
                                 (cell 5 (numV 0))
                                 (cell 4 (numV 1)))
                           (list (pointer 5 4)))))
(test (interp (parse `{ let {[p { malloc 3}]}
                         {let {[c {malloc 4}]}
                           {let {[a {malloc 5}]}
                             {begin
                               {free p}
                               {free a}}}}}) mt-env mt-store) (v*s (numV 0) (store
                                                                             (list (cell 15 (numV 10))
                                                                                   (cell 9 (numV 5))
                                                                                   (cell 8 (numV 0))
                                                                                   (cell 7 (numV 0))
                                                                                   (cell 6 (numV 0))
                                                                                   (cell 5 (numV 0))
                                                                                   (cell 4 (numV 1)))
                                                                             (list (pointer 5 4)))))
(test (interp (parse `{ let {[p { malloc 3}]}
                         {let {[c {malloc 4}]}
                           {let {[a {malloc 5}]}
                             {begin
                               {free a}
                               {free c}}}}}) mt-env mt-store) (v*s (numV 0) (store
                                                                             (list (cell 15 (numV 10))
                                                                                   (cell 9 (numV 5))
                                                                                   (cell 4 (numV 1))
                                                                                   (cell 3 (numV 0))
                                                                                   (cell 2 (numV 0))
                                                                                   (cell 1 (numV 0)))
                                                                             (list (pointer 1 3)))))
(test (interp (parse `{ let {[p { malloc 3}]}
                         {let {[c {malloc 4}]}
                           {let {[a {malloc 5}]}
                             {begin
                               {set-content! 11 2}
                               {free c}}}}}) mt-env mt-store) (v*s (numV 0) (store
                                                                             (list
                                                                              (cell 11 (numV 2))
                                                                              (cell 15 (numV 10))    
                                                                              (cell 14 (numV 0))
                                                                              (cell 13 (numV 0))
                                                                              (cell 12 (numV 0))
                                                                              (cell 11 (numV 0))
                                                                              (cell 10 (numV 0))
                                                                              (cell 9 (numV 5))
                                                                              (cell 4 (numV 1))
                                                                              (cell 3 (numV 0))
                                                                              (cell 2 (numV 0))
                                                                              (cell 1 (numV 0)))
                                                                             (list (pointer 10 5) (pointer 1 3)))))
