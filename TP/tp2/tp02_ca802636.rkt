; Cours 02 : Fonctions

#lang plait

;;;;;;;;;;;;;;;;;;;;;;;;
; Définition des types ;
;;;;;;;;;;;;;;;;;;;;;;;;

; Représentation des expressions
(define-type Exp
  [numE (n : Number)]
  [idE (s : Symbol)]
  [plusE (l : Exp) (r : Exp)]
  [subE (l : Exp) (r : Exp)]
  [multE (l : Exp) (r : Exp)]
  [appE (fun : Symbol) (arg : (Listof Exp))])

; Représentation des définitions de fonctions
(define-type FunDef
  [fd (name : Symbol) (par : (Listof Symbol)) (body : Exp)])

;;;;;;;;;;;;;;;;;;;;;;
; Analyse syntaxique ;
;;;;;;;;;;;;;;;;;;;;;;

(define (parse [s : S-Exp]) : Exp
  (cond
    [(s-exp-match? `NUMBER s) (numE (s-exp->number s))]
    [(s-exp-match? `SYMBOL s) (idE (s-exp->symbol s))]
    [(s-exp-match? `{+ ANY ...} s)
     (let ([sl (s-exp->list s)])
       (foldr plusE (numE 0) ( map parse (rest sl))))]
    [(s-exp-match? `{- ANY ANY} s)
     (let ([sl (s-exp->list s)])
       (subE (parse (second sl)) (parse (third sl))))]
    [(s-exp-match? `{* ANY ANY} s)
     (let ([sl (s-exp->list s)])
       (multE (parse (second sl)) (parse (third sl))))]
    [(s-exp-match? `{SYMBOL ANY ...} s)
     (let ([sl (s-exp->list s)])
       (if (< (length (rest sl)) 1) (error 'parse "invalid input")
           (appE (s-exp->symbol (first sl)) ( map parse (rest sl)))))]
    [else (error 'parse "invalid input")]))


(define (parse-fundef [s : S-Exp]) : FunDef
  (if (s-exp-match? `{define {SYMBOL SYMBOL SYMBOL ...} ANY} s)
      (let ([sl (s-exp->list s)])
        (let ([sl2 (s-exp->list (second sl))])
          (fd (s-exp->symbol (first sl2)) 
              (map s-exp->symbol ( rest sl2))
              (parse (third sl)))))
      (error 'parse-fundef "invalid input")))

;;;;;;;;;;;;;;;;;;
; Interprétation ;
;;;;;;;;;;;;;;;;;;

; Interpréteur
(define (interp [e : Exp] [fds : (Listof FunDef)]) : Number
  (type-case Exp e
    [(numE n) n]
    [(idE s) (error 'interp "free identifier")]
    [(plusE l r) (+ (interp l fds) (interp r fds))]
    [(subE l r) (- (interp l fds) (interp r fds))]
    [(multE l r) (* (interp l fds) (interp r fds))]
    [(appE f arg)
     (let [(fd (get-fundef f fds))]
       (if (not(= (length arg) (length (fd-par fd)))) ( error 'interp "wrong arity")
           (let [(args-list (map (lambda (x) (numE(interp x fds))) arg))]    
             ( interp (aux args-list (fd-par fd) (fd-body fd)) fds))))]))

(define (aux (arg : (Listof Exp) ) ( param : (Listof Symbol)) (body : Exp)) : Exp
  (if (<(length arg) 1) body
      (aux (rest arg) (rest param) (subst  (first arg) (first param) body))))
                
;[(appE f arg) (let [(fd (get-fundef f fds))]
;                    (interp (subst (numE (interp arg fds))
;                                   (fd-par fd)
;                                   (fd-body fd))
;                            fds))]
;
                



; Recherche d'une fonction parmi les définitions
(define (get-fundef [s : Symbol] [fds : (Listof FunDef)]) : FunDef
  (cond
    [(empty? fds) (error 'get-fundef "undefined function")]
    [(equal? s (fd-name (first fds))) (first fds)]
    [else (get-fundef s (rest fds))]))

; Substitution
(define (subst [what : Exp] [for : Symbol] [in : Exp]) : Exp
  (type-case Exp in
    [(numE n) in]
    [(idE s) (if (equal? for s) what in)]
    [(plusE l r) (plusE (subst what for l) (subst what for r))]
    [(subE l r) (subE (subst what for l) (subst what for r))]
    [(multE l r) (multE (subst what for l) (subst what for r))]
    [(appE f arg) (appE f (map (lambda (x) (subst what for x))arg))]))

;;;;;;;;;
; Tests ;
;;;;;;;;;

(define (interp-expr [e : S-Exp] [fds : (Listof S-Exp)]) : Number
  (interp (parse e) (map parse-fundef fds)))

(test (interp-expr `{double 3}
                   (list `{define {double x} {+ x x}}))
      6)

(test (interp-expr `{quadruple 3}
                   (list `{define {double x} {+ x x}}
                         `{define {quadruple x} {double {double x}}}))
      12)

( test ( interp-expr `{+ 1 {- 3 1} 3 {* 2 2} 5} empty ) 15)

( test ( interp-expr `{+} empty ) 0)
( test ( interp-expr `{+ 1} empty ) 1)
( test ( interp-expr `{+ 1 2} empty ) 3)
( test ( interp-expr `{+ 1 2 3 4 5} empty ) 15)

(test (interp-expr `{f 1 2 } (list `{define  {f x y} {+ x y} })) 3 )

( test/exn ( interp-expr `0 ( list `{ define {f} 42})) "invalid input")
( test ( interp-expr `{- 1 2} empty ) -1)
( test/exn ( interp-expr `{f 1}
                         ( list `{ define {f x y} {+ x y} })) "wrong arity")