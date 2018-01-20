
(define mp (lambda (x)
	(if (pair? x)
		(if (eq? (car x) ':) (list (mp (cdr x)))
			 (cons (mp (car x)) (mp (cdr x))) )
		x ) ))

(eval (mp '(begin

(define r2a : lambda (l) : 
 if (not : pair? l) l :
 if (pair? : car l) (r2 : append (car l) : cdr l) :
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
 begin (display l) (newline) :
 if (equal? n 0) '() :
 loopr2 (- n 1) (r2 l))

)))

