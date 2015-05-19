#lang postfix-dot-notation sweet-exp typed/racket/base

provide rmv
        rmv*
        hsh-rmv
        hsh-rmv*

require "hash-remove-multi.rkt"

: rmv :
  All (A)
    (Listof A) -> [Any -> (Listof A)]
define lst.rmv(elt)
  remove(elt lst)

: rmv* :
  All (A)
    (Listof A) -> [(Listof Any) -> (Listof A)]
define lst.rmv*(elts)
  remove*(elts lst)

: hsh-rmv :
  All (A B)
    (HashTable A B) -> [Any -> (HashTable A B)]
define hsh.hsh-rmv(key)
  hash-remove(hsh key)

: hsh-rmv* :
  All (A B)
    (HashTable A B) -> [(Listof Any) -> (HashTable A B)]
define hsh.hsh-rmv*(keys)
  hash-remove*(hsh keys)

