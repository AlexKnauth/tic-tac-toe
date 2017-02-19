#lang sweet-exp typed/racket/base

provide (all-defined-out)

require my-cond/iffy
        "utils/case-type/case-type.rkt"

define-type X 'X #:omit-define-syntaxes
define-type O 'O #:omit-define-syntaxes
: X : X
: O : O
define X 'X
define O 'O
define-predicate X? X
define-predicate O? O

define-type Side (U X O)

: other-side : Side -> Side
define other-side(side)
  case/type side
    X O
    O X

define-type Pos (List (U 0 1 2) (U 0 1 2))
define-predicate pos? Pos
: p : Integer Integer -> Pos ; this type could be more restrictive, but it's lenient (on purpose)
define p(x y)
  assert list(x y) pos?

define-type Board
  (HashTable Pos Side)

define all-poss
  for*/list ([y (in-range 3)]
             [x (in-range 3)]) : (Listof Pos)
    p(x y)

