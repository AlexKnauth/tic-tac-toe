#lang postfix-dot-notation sweet-exp typed/racket/base

provide (all-defined-out)

require racket/match
        racket/list
        syntax/parse/define
        my-cond/iffy
        "utils/case-type/case-type.rkt"
        for-syntax racket/base
                   syntax/parse

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

;; ------------------------------------------------------------------------

: board-winner : Board -> (U Side #f)
define board-winner(board)
  define 0-0
    hash-ref board p(0 0) #f
  define 1-1
    hash-ref board p(1 1) #f
  define 2-2
    hash-ref board p(2 2) #f
  or
    and 0-0
      or
        and (equal? 0-0 (hash-ref board '(0 1) #f))
          (equal? 0-0 (hash-ref board '(0 2) #f))
          0-0
        and (equal? 0-0 (hash-ref board '(1 0) #f))
          (equal? 0-0 (hash-ref board '(2 0) #f))
          0-0
        and (equal? 0-0 1-1)
          (equal? 0-0 2-2)
          0-0
    and 1-1
      or
        and (equal? 1-1 (hash-ref board '(0 1) #f))
          (equal? 1-1 (hash-ref board '(2 1) #f))
          1-1
        and (equal? 1-1 (hash-ref board '(1 0) #f))
          (equal? 1-1 (hash-ref board '(1 2) #f))
          1-1
        and (equal? 1-1 (hash-ref board '(0 2) #f))
          (equal? 1-1 (hash-ref board '(2 0) #f))
          1-1
    and 2-2
      or
        and (equal? 2-2 (hash-ref board '(0 2) #f))
          (equal? 2-2 (hash-ref board '(1 2) #f))
          2-2
        and (equal? 2-2 (hash-ref board '(2 0) #f))
          (equal? 2-2 (hash-ref board '(2 1) #f))
          2-2



: board-full? : Board -> Boolean
define board-full?(board)
  {9 <= board.hash-count}

;; ------------------------------------------------------------------------

: transform-board : Board Transform -> Board
define transform-board(board t)
  for/hash ([([k : Pos] [v : Side]) (in-hash board)]) : Board
    values[k.t v]

define-simple-macro
  sym-trans expr
  #:with [x-id y-id]
  syntax-local-introduce #'[x y]
  λ ([pos : Pos])
    match-define list(x-id y-id) pos
    assert expr pos?

: symetry-transforms : (Listof Transform)
define symetry-transforms
  list
    sym-trans list(   x       y   )
    sym-trans list({2 - x}    y   )
    sym-trans list(   x    {2 - y})
    sym-trans list({2 - x} {2 - y})
    sym-trans list(   y       x   )
    sym-trans list({2 - y}    x   )
    sym-trans list(   y    {2 - x})
    sym-trans list({2 - y} {2 - x})

define-type Transform [Pos -> Pos]

: board=?/symetry : Board Board -> Boolean
define board=?/symetry(b1 b2)
  and
    {b1.hash-count = b2.hash-count}
    for/or ([t (in-list symetry-transforms)]) : Boolean
      equal? transform-board(b1 t) b2

;; ------------------------------------------------------------------------

: display-board : Board -> Void
define display-board(board)
  displayln " ------- "
  for ([y in-range(3)])
    display " | "
    for ([x in-range(3)])
      display (hash-ref board (assert list(x y) pos?) (λ () " "))
    display " | "
    newline()
  displayln " ------- "

;; ------------------------------------------------------------------------

: spaces->board : (Listof (Listof (U Side #f))) -> Board
define spaces->board(spaces)
  unless {spaces.length = 3}
    error('spaces->board "bad")
  for/hash ([pos in-list(all-poss)]
            [spc in-list(append*(spaces))]
            #:when spc) : Board
    values(pos assert(spc))

