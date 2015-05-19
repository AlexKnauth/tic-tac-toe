#lang postfix-dot-notation sweet-exp typed/racket

provide partition2

: partition2 :
  All (A B)
    (Listof (U A B))
    [Any -> Boolean : A]
    [Any -> Boolean : B]
    ->
    values (Listof A) (Listof B)
define partition2(lst pred1? pred2?)
  define-values [1s 2s]
    (inst partition A (U A B)) pred1? lst
  unless (andmap pred2? 2s)
    error('partition2 "this should never happen")
  values(1s 2s)

;; wish list: partition-multi
;
; : partition-multi :
;   All (A ...)
;     (Listof (U A ...))
;     (List [Any -> Boolean : #:+ A] ...)
;     ->
;     (List (Listof A) ...)

