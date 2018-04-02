
(define mp (lambda (x)
	(if (pair? x)
		(if (eq? (car x) ':) (list (mp (cdr x)))
			 (cons (mp (car x)) (mp (cdr x))) )
		x ) ))

(eval (mp '(begin

(define last : lambda (l) : 
 if (not : pair? l) l :
 if (not : pair? : cdr l) l :
 last : cdr l)

(define butlast : lambda (l) :
 if (not : pair? l) '() :
 if (not : pair? : cdr l) '() :
 cons (car l) : butlast : cdr l)

(define length : lambda (l) : 
 if (not : pair? l) 0 :
 + 1 : length : cdr l)

(define r2a : lambda (l) : 
 if (not : pair? l) l :
 if (pair? : car l) (r2 : append (car l) : cdr l) :
 if (eq? (car l) 'suc) (cdr l) :
 if (eq? (car l) 'H) (cons (cadr l) : cons (list (cadr l) (caddr l)) : cdddr l) :
 if (eq? (car l) 'R1) (cons (cadr l) : cons (cadr l) : cddr l) :
 if (eq? (car l) 'R2) (cons (cadr l) : cons (caddr l) : cons (cadr l) : cons (caddr l) : cdddr l) 
 l)

(define r : lambda (l) :
 if (not : pair? l) l :
 let ((l1 (map r l))) : 
 if (pair? : car l1) (append (car l1) (cdr l1)) 
 l1)

(define r2 : lambda (l) : r : r2a l)

(define loopr2 : lambda (n l) :
 begin (display n) (display " ") (display l) (newline) :
 if (equal? n 0) '() :
 loopr2 (- n 1) (r2 l))

(loopr2 10 '(R1 H suc 0))

(define simplif : lambda (x) :
 if (not : pair? x) x :
 if (not : pair? : cdr x) (car x) 
 x)
 
(define memo '())

(define find : lambda (a memo) :
 if (not : pair? memo) '#f :
 begin (display "a = ") (display a) (newline) 
       (display "memo = ") (display memo) (newline) :
 if (equal? a : caar memo) (cdar memo) :
 find a : cdr memo)

(define psi : lambda (a) :
 let ((m : find a memo)) :
 if m (begin (display "found : ") (display m) (newline) m) :
 let ((b : psi2 a)) 
  (display "psi ") (display a) (display " = ") (display b) (newline)
  (set! memo : cons (cons a b) memo)
  b)

(define psi1 : lambda (a) : 
 if (not : pair? a) a :
 if (pair? : car a) (psi : append (car a) (cdr a)) :
 if (equal? (car a) '0) '(H suc 0) :
 if (equal? 'suc : car a)
  (let ((b : psi : cdr a)) :
   if (and (equal? '(0) : last b)
           (equal? '(suc) : last : butlast b)) 
    (list 'R1 (simplif : butlast : butlast b) 'suc '0)
    (list 'psi a)) :
 if (and (equal? 'H : car a) (>= (length a) 3)) 
  (limit (psi : cddr a)
         (psi : cdr a)
         (psi : cons (cadr a) : cons (list (cadr a) (caddr a)) : cdddr a)) :
 if (and (equal? 'R1 : car a) (>= (length a) 2)) 
  (limit (psi : cddr a)
         (psi : cdr a)
         (psi : cons (cadr a) : cdr a)) 
 a)

(define myappend : lambda (a b) :
 if (not : pair? a) (cons a b) : 
 append a b)

(define commonstart : lambda (a b) :
 if (not : pair? a) (list '() a b) :
 if (not : pair? b) (list '() a b) :
 if (not : equal? (car a) (car b)) (list '() a b) :
 let ((c : commonstart (cdr a) (cdr b))) :
 let ((com : car c) (dif1 : cadr c) (dif2 : caddr c)) :
 list (cons (car a) com) dif1 dif2)

(define limit : lambda (a b c) :
 if (and (equal? (cdr a) (cddr b))
         (equal? (cdr a) (cddr c))
         (equal? a (cdr b))
         (equal? (car b) (car c))
         (equal? (cadr c) (list (car b) (cadr b))))
  (cons 'H b) :
 if (and (equal? a (myappend (cadr b) (cddr b)))
         (equal? (car b) (car c))
         (equal? (cadr c) (list (car b) (cadr b)))
         (equal? (cddr b) (cddr c)))
  (cons 'H b) :
 let ((d : commonstart b c)) :
 let ((com : car d) (difb : cadr d) (difc : caddr d)) :
 if (and (pair? com)
         (equal? com : butlast : car difc)
         (equal? (car difb) (car : last : car difc))
         (equal? a : myappend (car difb) (cdr difb))
         (equal? (cdr difb) (cdr difc)))
  (cons 'H : cons com difb) :
 if (and (equal? a : cdr b)
         (equal? b : cdr c)
         (equal? (car b) (car c))
         (equal? (car c) (cadr c)))
  (cons 'R1 b) :
 list 'limit a b c)

;(display : psi '(H H suc 0))
(newline)

)))

