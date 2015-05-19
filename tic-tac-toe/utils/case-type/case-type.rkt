#lang sweet-exp typed/racket/base

provide case/type

require my-cond/define-syntax-parser
        "case-pred.rkt"
        for-syntax racket/base
                   syntax/parse
                   racket/syntax

define-syntax-parser case/type #:stx stx
  [(case/type e:expr (~and clause [:expr :expr ...+]) ...)
   #:with x
   (generate-temporary #'e)
   (syntax/loc stx (case/type e #:id x clause ...))]
  [(case/type e:expr #:id x:id
     [t:expr body:expr ...+] ...
     (~and else-clause [(~literal else) ~! :expr ...+]))
   (syntax/loc stx
     (case/pred e #:id x
       [(make-predicate t) body ...] ...
       else-clause))]
  [(case/type e:expr #:id x:id (~and clause [:expr :expr ...+]) ...)
   #:with covered-id:id
   (syntax-parse #'e
     [id:id #'id]
     [_ #'x])
   #:with else-body
   #`(typecheck-fail #,stx #:covered-id covered-id)
   (syntax/loc stx
     (case/type e #:id x clause ... [else else-body]))]

