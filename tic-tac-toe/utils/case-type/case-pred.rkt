#lang sweet-exp racket/base

provide case/pred

require my-cond/define-syntax-parser
        for-syntax racket/base
                   syntax/parse
                   racket/syntax

define-syntax-parser case/pred #:stx stx
  [(case/pred e:expr (~and clause [:expr :expr ...+]) ...)
   #:with x
   (generate-temporary #'e)
   (syntax/loc stx (case/pred e #:id x clause ...))]
  [(case/pred e:expr #:id x:id
     [pred?:expr body:expr ...+] ...
     (~and else-clause [(~literal else) ~! :expr ...+]))
   (syntax/loc stx
     (let ([x e])
       (cond [(pred? x) body ...] ...
             else-clause)))]
  [(case/pred e:expr #:id x:id (~and clause [:expr :expr ...+]) ...)
   #:with else-body
   #`(raise-syntax-error #f (format "no pred matched for ~v" x) #'#,stx #'e)
   (syntax/loc stx
     (case/pred e #:id x clause ... [else else-body]))]

