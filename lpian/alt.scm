
(define call/cc call-with-current-continuation)

(define lctxs '())

(define curctx '((0 0 0)))

(define (mk-ctx prio lincr rincr fn) 
 (list (list prio lincr rincr) fn) )

(define (prio-ctx ctx) (caar ctx))
(define (lincr-ctx ctx) (cadar ctx))
(define (rincr-ctx ctx) (caddar ctx))
(define (fn-ctx ctx) (cadr ctx))

(define (insctx ctx ctxs)
 (if (not (pair? ctxs)) (list ctx)
  (if (>= (prio-ctx ctx) (prio-ctx (car ctxs))) (cons ctx ctxs)
   (cons (car ctxs) (insctx ctx (cdr ctxs))) ) ) )

(define-syntax alt 
 (syntax-rules ()
  ((_ a b) (if (alt2 '#t '#f) a b)) ))

(define (alt1 a b)
 (call/cc (lambda (k)
  (set! lctxs (cons (lambda () (k b)) lctxs))
  (k a))))

(define (alt2 a b)
 (call/cc (lambda (k)
  (set! lctxs (insctx (mk-ctx (+ (prio-ctx curctx) (lincr-ctx curctx))
                              (lincr-ctx curctx)
                              (rincr-ctx curctx)
                              (lambda () (k a)) ) 
               (insctx (mk-ctx (+ (prio-ctx curctx) (rincr-ctx curctx))
                               (lincr-ctx curctx)
                               (rincr-ctx curctx) 
                               (lambda () (k b)) ) lctxs)))
  (end) )) )

(define (end)
 (if (not (pair? lctxs)) 'exhausted
  (let ((ctx (car lctxs)))
   (set! lctxs (cdr lctxs))
   (set! curctx ctx)
   ((fn-ctx ctx)) ) ) )

(define (test-depth)
 (set! curctx (mk-ctx 0 1 1 '()))
 (begin (alt (begin (display 'a) (alt (display 'b) (display 'c)))
             (begin (display 'd) (alt (display 'e) (display 'f))) ) (end)) )

(define (test-breadth)
 (set! curctx (mk-ctx 0 -1 -1 '()))
 (begin (alt (begin (display 'a) (alt (display 'b) (display 'c)))
             (begin (display 'd) (alt (display 'e) (display 'f))) ) (end)) )


