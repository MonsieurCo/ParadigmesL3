; Cours 06 : Interpréteur pour le lambda-calcul à compléter

#lang plait

;;;;;;;;;;;;;;;
; Expressions ;
;;;;;;;;;;;;;;;

; Langage intermédiaire
(define-type ExpS
  [idS (s : Symbol)]
  [lamS (pars : (Listof Symbol)) (body : ExpS)]
  [appS (fun : ExpS) (args : (Listof ExpS))]
  [letS (pars : (Listof Symbol)) (args : (Listof ExpS)) (body : ExpS)]

  [numS (n : Number)]
  [add1S]
  [plusS]
  [multS]

  [trueS]
  [falseS]
  [ifS (cnd : ExpS) (l : ExpS) (r : ExpS)]  
  [zeroS]

  [pairS]
  [fstS]
  [sndS]
  [sub1S]
  [minusS]
  
  [divS]
 
  [letrecS (par : Symbol) (arg : ExpS) (body : ExpS)])

; Le langage du lambda-calcul
(define-type Exp
  [idE (s : Symbol)]
  [lamE (par : Symbol) (body : Exp)]
  [appE (fun : Exp) (arg : Exp)])

;;;;;;;;;;;;;;;;;;;;;;
; Analyse syntaxique ;
;;;;;;;;;;;;;;;;;;;;;;

(define (compose f g)
  (lambda (x) (f (g x))))

(define (parse [s : S-Exp]) : ExpS
  (cond
    [(s-exp-match? `NUMBER s) (numS (s-exp->number s))]

    ; ensembles de symboles prédéfinis
    [(s-exp-match? `add1 s) (add1S)]
    [(s-exp-match? `+ s) (plusS)]
    [(s-exp-match? `sub1 s) (sub1S)]
    [(s-exp-match? `- s) (minusS)]
    [(s-exp-match? `* s) (multS)]
    [(s-exp-match? `/ s) (divS)]
    [(s-exp-match? `true s) (trueS)]
    [(s-exp-match? `false s) (falseS)]
    [(s-exp-match? `zero? s) (zeroS)]
    [(s-exp-match? `pair s) (pairS)]
    [(s-exp-match? `fst s) (fstS)]
    [(s-exp-match? `snd s) (sndS)]
    
    [(s-exp-match? `SYMBOL s) (idS (s-exp->symbol s))]
    [(s-exp-match? `{lambda {SYMBOL SYMBOL ...} ANY} s)
     (let ([sl (s-exp->list s)])
       (lamS (map s-exp->symbol (s-exp->list (second sl))) (parse (third sl))))]
    [(s-exp-match? `{let {[SYMBOL ANY] [SYMBOL ANY] ...} ANY} s)
     (let ([sl (s-exp->list s)])
       (let ([substs (map s-exp->list (s-exp->list (second sl)))])
         (letS (map (compose s-exp->symbol first) substs)
               (map (compose parse second) substs)
               (parse (third sl)))))]
    [(s-exp-match? `{if ANY ANY ANY} s)
     (let ([sl (s-exp->list s)])
       (ifS (parse (second sl)) (parse (third sl)) (parse (fourth sl))))]
    [(s-exp-match? `{letrec {[SYMBOL ANY]} ANY} s)
     (let ([sl (s-exp->list s)])
       (let ([substs (s-exp->list (first (s-exp->list (second sl))))])
         (letrecS (s-exp->symbol (first substs))
                  (parse (second substs))
                  (parse (third sl)))))]  
    [(s-exp-match? `{ANY ANY ANY ...} s)
     (let ([sl (s-exp->list s)])
       (appS (parse (first sl)) (map parse (rest sl))))]
    [else (error 'parse "invalid input")]))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Retrait du sucre syntaxique ;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define (fold-pars pars body)
(if (= (length pars) 1)
    (lamE  (first pars) (desugar body))
    (lamE (first pars) (fold-pars (rest pars) body))))

(define (fold-app fun args)
  (if (= (length args) 1)
      (appE (desugar fun) (desugar (first args)))
      (appE (fold-app fun (rest args)) (desugar (first args)))))


(define (numerise n)
  (cond
    [(equal? n 0) (idE 'x)]
    [else (appE (idE 'f) (numerise (- n 1 )))])) 

  
;  {let {[id rhs]} body} <=>  {{lambda {id} body} rhs}

    (define (desugar [e : ExpS]) : Exp
      (type-case ExpS e
        [(idS s) (idE s)]
        [(lamS pars body) (if (>= (length pars) 1)
                              (fold-pars pars body)
                              (error 'desugar "not implemented"))]
        [(appS fun args) (if (>= (length args) 1)
                             (fold-app fun (reverse args))
                             (error 'desugar "not implemented"))]
        [(letS pars args body) (desugar (appS (lamS pars body) args))]
        [(numS n)  ( lamE 'f  (lamE 'x (numerise n)))]
        [(add1S) ( lamE 'n (lamE 'f (lamE 'x (appE ( idE 'f )(appE (appE (idE 'n) (idE 'f)) (idE 'x))))) )]
        [(plusS) (lamE 'n (lamE 'm (appE (appE (idE 'm)  ( lamE 'n (lamE 'f (lamE 'x (appE ( idE 'f )(appE (appE (idE 'n) (idE 'f)) (idE 'x))))) )) (idE 'n))))]
        [(multS) (lamE 'n (lamE 'm (appE (appE (idE 'm) (appE (desugar (plusS)) (idE 'n))) (desugar (numS 0)))))]
        [(trueS) (lamE 'x (lamE 'y (idE 'x)))]
        [(falseS)(lamE 'x (lamE 'y (idE 'y)))]
        [(ifS cnd  l r ) ( appE (appE (appE (desugar cnd) ( lamE 'd (desugar l))) ( lamE 'd (desugar r))) (idE '_))   ]
        ; [(zeroS) (lamE 'n (appE  (idE 'n) (appE (lamE 'x (desugar (falseS))) (desugar (trueS) )) ))]
        [(zeroS) (lamE 'n (appE (appE (idE 'n) (lamE 'x (desugar (falseS))) ) (desugar (trueS) )) )]
        [(pairS) (lamE 'x (lamE 'y (lamE 'sel (appE (appE (idE 'sel ) (idE 'x)) (idE 'y) ))))]
        [(fstS) (lamE 'p (appE (idE 'p) (desugar (trueS))))]
        [(sndS) (lamE 'p (appE (idE 'p) (desugar (falseS))))]
        [(sub1S) (lamE 'n (appE (desugar (fstS))(appE (appE (idE 'n) (shift)) (appE (appE (desugar (pairS)) (desugar (numS 0))) (desugar (numS 0))))))]
        [(minusS) (lamE 'n (lamE 'm (appE (appE (idE 'm)(desugar (sub1S)))  (idE 'n))))]
        [(letrecS par arg body) (appE (lamE par (desugar body)) (appE (mk-rec) (lamE par (desugar arg))))

                                      ]








         
        

;(λfac.fac (λf.λx.f (f (f (f (f (f x))))))) ((λbody-proc.(λfX.fX fX) (λfX.(λf.body-proc f)(λx.fX fX x)))
; (λfac.λn.(λn.n (λ_.λx.λy.y) (λx.λy.x)) n (λ_.λf.λx.f x) (λ_.(λn.λm.n
;((λn.λm.n (λn.λf.λx.f (n f x)) m) m) (λf.λx.x)) n (fac ((λn.λm.m ((λshift.λn.(λp.p
;(λx.λy.x))(n shift ((λx.λy.λsel.sel x y)(λf.λx.x) (λf.λx.x))))(λp.(λx.λy.λsel.sel x
;y)((λp.p (λx.λy.y)) p) ((λn.λf.λx.f (n f x))((λp.p (λx.λy.y)) p)))) n) n (λf.λx.fx)))) _))

;"(λfac.fac (λf.λx.f (f (f (f (f (f x))))))) ((λbody-proc.(λfX.fX fX) (λfX.(λf.body-proc f)(λx.fX fX x)))
;(λfac.fac (λn.(λn.n (λx.λx.λy.y) (λx.λy.x)) n (λd.λf.λx.f x) (λd.(λn.λm.m ((λn.λm.m (λn.λf.λx.f (n f x))
;n) n) (λf.λx.x)) n (fac ((λn.λm.m (λn.(λp.p (λx.λy.x))(n (λp.(λx.λy.λsel.sel x y)((λp.p (λx.λy.y)) p)
;((λn.λf.λx.f (n f x))((λp.p (λx.λy.y)) p))) ((λx.λy.λsel.sel x y)(λf.λx.x) (λf.λx.x)))) n) n (λf.λx.f x))))
; (λf.λx.x))))"

        
;"(λfac.fac (λf.λx.f (f (f (f (f (f x))))))) ((λbody-proc.(λfX.fX fX) (λfX.(λf.body-proc f)(λx.fX fX x)))
;
;          (λn.(λn.n (λx.λx.λy.y) (λx.λy.x)) n (λd.λf.λx.f x) (λd.(λn.λm.m ((λn.λm.m (λn.λf.λx.f (n f x)) n) n) (λf.λx.x))
; n (fac ((λn.λm.m (λn.(λp.p (λx.λy.x))(n (λp.(λx.λy.λsel.sel x y)((λp.p (λx.λy.y)) p) ((λn.λf.λx.f (n f x))
;((λp.p (λx.λy.y)) p))) ((λx.λy.λsel.sel x y)(λf.λx.x) (λf.λx.x)))) n) n (λf.λx.f x)))) (λf.λx.x)))"



        
        
;"(λfac.fac (λf.λx.f (f (f (f (f (f x))))))) ((λbody-proc.(λfX.fX fX) (λfX.λf.body-proc f (λx.fX fX x)))
;(λn.(λn.n (λx.λx.λy.y) (λx.λy.x)) n (λd.λf.λx.f x) (λd.(λn.λm.m ((λn.λm.m (λn.λf.λx.f (n f x)) n) n)
; (λf.λx.x)) n (fac ((λn.λm.m (λn.(λp.p (λx.λy.x))(n (λp.(λx.λy.λsel.sel x y)((λp.p (λx.λy.y)) p)
; ((λn.λf.λx.f (n f x))((λp.p (λx.λy.y)) p))) ((λx.λy.λsel.sel x y)(λf.λx.x) (λf.λx.x)))) n) n (λf.λx.f x))))
;(λf.λx.x)))"




        

;"(λfac.fac (λf.λx.f (f (f (f (f (f x))))))) ((λbody-proc.(λfX.fX fX) (λfX. (λf.body-proc f) (λx.fX fX x))
;(λn.(λn.n (λx.λx.λy.y) (λx.λy.x)) n (λd.λf.λx.f x)
;(λd.(λn.λm.m ((λn.λm.m (λn.λf.λx.f (n f x)) n) n) (λf.λx.x)) n
;(fac ((λn.λm.m (λn.(λp.p (λx.λy.x))(n (λp.(λx.λy.λsel.sel x y)
;((λp.p (λx.λy.y)) p) ((λn.λf.λx.f (n f x))((λp.p (λx.λy.y)) p)))
;((λx.λy.λsel.sel x y)(λf.λx.x) (λf.λx.x)))) n) n (λf.λx.f x)))) (λf.λx.x)))"










        
;"(λfac.fac (λf.λx.f (f (f (f (f (f x))))))) (λn.(λn.n (λx.λx.λy.y) (λx.λy.x)) n
;(λd.λf.λx.f x) (λd.(λn.λm.m ((λn.λm.m (λn.λf.λx.f (n f x)) n) n) (λf.λx.x)) n
;(fac ((λn.λm.m (λn.(λp.p (λx.λy.x))(n (λp.(λx.λy.λsel.sel x y)((λp.p (λx.λy.y)) p)
;((λn.λf.λx.f (n f x))((λp.p (λx.λy.y)) p)))
;((λx.λy.λsel.sel x y)(λf.λx.x) (λf.λx.x)))) n) n (λf.λx.f x)))) (λf.λx.x))"

;"(λfac.fac (λf.λx.f (f (f (f (f (f x)))))))(λbody-proc.(λfX.fX fX)(λfX.λf.body-proc f) (λx.fX fX x))"



        
;"(λfac.fac (λf.λx.f (f (f (f (f (f x)))))))(λn.zero ? n (λd.λf.λx.f x)
;(λd.(λn.λm.m ((λn.λm.m (λn.λf.λx.f (n f x)) n) n) (λf.λx.x)) n
;(fac ((λn.λm.m (λn.(λp.p (λx.λy.x))(n (λp.(λx.λy.λsel.sel x y)((λp.p (λx.λy.y)) p)
;((λn.λf.λx.f (n f x))((λp.p (λx.λy.y)) p))) ((λx.λy.λsel.sel x y)(λf.λx.x)
;(λf.λx.x)))) n) n (λf.λx.f x)))) (λf.λx.x))"

 
;shift =>  (lamE 'p (appE (appE (desugar (pairS)) (appE (desugar (snds)) (idE 'p))) (appE (desugar (sndS)) idE 'p)))

 ;λx.λy.x≡ true
;λx.λy.y≡ false

                                          
        
        [else (error 'desugar "not implemented")]))
;((λbody-proc.(λfX.fX fX)(λfX.(λf.body-procf) (λx.fX fX x))))
;((λbody-proc.(λfX.fX fX) (λfX.(λf.body-proc f)(λx.fX fX x)))
(define (mk-rec) (lamE 'body-proc (appE
                                   (lamE 'fX (appE (idE 'fX) (idE 'fX)))
                                   (lamE 'fX
                                         ( appE
                                           (lamE 'f (appE ( idE 'body-proc) (idE 'f)))
                                           (lamE 'x (appE (appE (idE 'fX) (idE 'fX)) (idE 'x))))))))




                       
                       ; (appE
                        ; (lamE 'fX (appE (idE 'fX) (idE 'fX)))
                         ;      (lamE 'fX (appE (appE (appE (lamE 'f ( idE 'body-proc) (idE 'f))
                          ;  (lamE 'x (appE (appE (idE 'fX) (idE 'fX)) (idE 'x)))))))))                                    

(define (shift)
  (lamE 'p (appE (appE (desugar (pairS)) (appE (desugar (sndS)) (idE 'p))) (appE  (desugar (add1S)) (appE (desugar (sndS)) (idE 'p))))))

    ;;;;;;;;;;;;;;;;;;
    ; Interprétation ;
    ;;;;;;;;;;;;;;;;;;

    ; Substitution
    (define (subst [what : Exp] [for : Symbol] [in : Exp]) : Exp
      (type-case Exp in
        [(idE s) (if (equal? s for) what in)]
        [(lamE par body) (if (equal? par for) in (lamE par (subst what for body)))]
        [(appE fun arg) (appE (subst what for fun) (subst what for arg))]))

    ; Interpréteur (pas de décente dans un lambda)
    (define (interp [e : Exp]) : Exp
      (type-case Exp e
        [(appE fun arg)
         (type-case Exp (interp fun)
           [(lamE par body) (interp (subst (interp arg) par body))]
           [else e])]
        [else e]))

    ; Concaténation de chaînes de caractères contenues dans une liste
    (define (strings-append [strings : (Listof String)]) : String
      (foldr string-append "" strings))

    ; Affichage lisible d'une lambda-expression
    (define (expr->string [e : Exp]) : String
      (type-case Exp e
        [(idE s) (symbol->string s)]
        [(lamE par body) (strings-append (list "λ" (symbol->string par) "." (expr->string body)))]
        [(appE fun arg)
         (let ([fun-string (if (lamE? fun)
                               (strings-append (list "(" (expr->string fun) ")"))
                               (expr->string fun))]
               [arg-string (if (idE? arg)
                               (expr->string arg)
                               (strings-append (list "(" (expr->string arg) ")")))])
           (if (and (lamE? fun) (not (idE? arg)))
               (string-append fun-string arg-string)
               (strings-append (list fun-string " " arg-string))))]))

    ; Transforme une expression en nombre si possible
    (define (expr->number [e : Exp]) : Number
      (type-case Exp (interp e)
        [(lamE f body-f)
         (type-case Exp (interp body-f)
           [(lamE x body-x)
            (destruct body-x f x)]
           [else (error 'expr->number "not a number")])]
        [else (error 'expr->number "not a number")]))
          
    ; Compte le nombre d'application de f à x
    (define (destruct [e : Exp] [f : Symbol] [x : Symbol]) : Number
      (type-case Exp (interp e)
        [(idE s) (if (equal? s x)
                     0
                     (error 'expr->number "not a number"))]
        [(lamE par body) (error 'expr->number "not a number")]
        [(appE fun arg) (if (equal? fun (idE f))
                            (+ 1 (destruct arg f x))
                            (error 'expr->number "not a number"))]))


    ; Transforme une expression en booléen si possible
    (define (expr->boolean [e : Exp]) : Boolean
      (type-case Exp (interp e)
        [(lamE x body-x)
         (type-case Exp (interp body-x)
           [(lamE y body-y)
            (type-case Exp (interp body-y)
              [(idE s) (cond
                         ((equal? x s) #t)
                         ((equal? y s) #f)
                         (else (error 'expr->boolean "not a boolean")))]
              [else (error 'expr->boolean "not a boolean")])]
           [else (error 'expr->boolean "not a boolean")])]
        [else (error 'expr->boolean "not a boolean")]))

    ;;;;;;;;;
    ; Tests ;
    ;;;;;;;;;

    (define (interp-number expr)
      (expr->number (desugar (parse expr))))

    (define (interp-boolean expr)
      (expr->boolean (desugar (parse expr))))

    (test(expr->string (desugar (parse `{{lambda{x y z}body}a b c})))"(λx.λy.λz.body) a b c")
    (test(expr->string (desugar (parse `{{lambda{x y z u v w}body}a b c r s t})))"(λx.λy.λz.λu.λv.λw.body) a b c r s t")
( test
(expr->string ( desugar ( parse `{ let {[x a] [y b] [z c]} body })))
"(λx.λy.λz.body) a b c")

( test ( interp-number `10) 10)
( test ( interp-number `{ add1 1}) 2)
( test ( interp-number `{+ 1 2}) 3)
( test ( interp-number `{* 3 4}) 12)
( test ( interp-boolean ` true ) #t)
( test ( interp-boolean ` false ) #f)
( test ( interp-number `{ if true 0 1}) 0)
( test ( interp-number `{ if false 0 1}) 1)
( test ( interp-boolean `{ zero? 0}) #t)
( test ( interp-boolean `{ zero? 1}) #f)
( test ( interp ( desugar ( parse `{ fst { pair a b} }))) (idE 'a))
( test ( interp ( desugar ( parse `{ snd { pair a b} }))) (idE 'b))
( test ( interp-number `{ sub1 2}) 1)
( test ( interp-number `{ sub1 5}) 4)
( test ( interp-number `{ sub1 12}) 11)
( test ( interp-number `{ sub1 20}) 19)
( test ( interp-number `{ sub1 1}) 0)
( test ( interp-number `{- 4 2}) 2)
( test ( interp-number `{- 1 2}) 0)

( expr->string (desugar (parse `{ letrec {[fac { lambda {n} { if { zero? n}1{* n { fac {- n 1} } } } }]}{ fac 6} })))

(test ( interp-number `{ letrec {[fac { lambda {n} { if { zero? n}1{* n { fac {- n 1} } } } }]}{ fac 6} })720)
(test (interp-number`{letrec {[fac {lambda {n} {lambda {a}
                                     {if {zero? n}
                                         a
                                         (fac (- n 1)(+ a 1)) }}}]}  
                       {fac 10 3}}) 13) 