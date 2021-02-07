#lang plait

(define (syracuse [n : Number]) : Number
  (if (even? n )
      (/ n 2)
      (+ (* 3 n) 1 )))

;ma version 
(define (somme [L : (Listof Number )]) : Number
  (foldl + 0 L) 
  )
; correction QUESTION 3
(define (somme_corr [L : (Listof Number)] ) : Number
  (if (empty? L )
      0
      (+ (first L) (somme (rest L)))))
; correction q3 avec un fold
(define (somme2 [L : (Listof Number)] ) : Number
  (foldl + 0 L))
;QUESTION 4
;(letrec(Append [LG : (Listof 'a)]
;               [LD : (Listof 'a)]) : (Listof 'a )
;(Append (cons (first LD) LG ) (rest LD)))


;correction
(define (Append1 [LG : (Listof 'a )] [LD : (Listof 'a)]) : (Listof 'a)
  (foldr cons LD LG ))
(Append1 '(1 2 3 4) '(5 6 7 8 ))
;correction 2 q4
(define (Append2 [LG : (Listof 'a )] [LD : (Listof 'a)]) : (Listof 'a)
  (if (empty? LG )
      LD
      (cons (first LG ) (Append2 ( rest LG) LD ))))

;QUESTION 5
; c'est cohérent

;QUESTION 6
(define (Map [f : ('a -> 'b )]  [L : (Listof 'b )]) : (Listof 'b)
  (if (empty? L)
      empty
      ( cons ( f (first L)) (Map f (rest L)))))

; (foldr f acc (e1 e2 .... eN) c'est (f e1 (e2 .... ( feN acc)...)
(define (Foldr [f : ('a 'b -> 'b )] [acc : 'b]  [L : (Listof 'a )]) : 'b
  (if (empty? L)
      acc
      (f (first L) (Foldr f acc (rest L)))))

; foldl appelons val la valeur de (f e1 acc) 
(define (Foldl f acc L)
  (if (empty? L )
      acc
      (Foldl f (f (first L)acc  )  (rest L) )))
;

(define-type (Couple 'a 'b); important de mettre les type des param sinon dès la premiere utilisation on definira les type definitivement sinon
  [couple ( fst : 'a ) (snd : 'b)])

(define-type (Option 'a)
  [vide]
  [element (value : 'a)])

(define (find [AL : (Listof (Couple 'key 'value))] [key : 'key]) : (Option 'value)
  (cond
    [(empty? AL) (vide)]
    [(equal? (couple-fst (first AL)) key) ( element (couple-snd (first AL)))]
    [else (find (rest AL) key)]))

(define couples (list (couple 'x 3 ) (couple 'y 7)))
(test (find couples 'y) (element 7))
(test (find couples 'z ) (vide))
; correction

;Arbres binaire

(define-type ArbreBinaire 
  [Feuille (val : Number)]
  ([Noeud (op : Number Number -> Number)
          ( fg : ArbreBinaire)
          ( fd : ArbreBinaire)])

 (define (eval  (A : ArbreBinaire)) : Number
   (type-case ArbreBinaire arbre
       [(Feuille val) val]
     [(Noeud op fd fg) (op (eval fd) (eval fg))])) 

       
  

  