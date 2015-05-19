#lang postfix-dot-notation sweet-exp typed/racket/base

provide rnd-elt

: rnd-elt :
  All (A)
    (Listof A) -> A
define rnd-elt(lst)
  list-ref lst random(lst.length)

