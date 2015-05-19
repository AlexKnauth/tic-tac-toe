#lang postfix-dot-notation sweet-exp typed/racket

provide hash-remove*

: hash-remove* :
  All (A B)
    (HashTable A B) (Listof Any) -> (HashTable A B)
define hash-remove*(hsh lst)
  for/fold ([hsh : (HashTable A B) hsh]) ([key (in-list lst)])
    hash-remove hsh key

