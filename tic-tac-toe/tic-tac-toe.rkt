#lang postfix-dot-notation sweet-exp typed/racket/base

provide (all-defined-out)

require racket/list
        racket/match
        racket/bool
        syntax/parse/define
        my-cond/iffy
        syntax/location
        "utils/rmv.rkt"
        "utils/rnd-elt.rkt"
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

struct play-result ([board : Board] [winner : (U Side #f)] [moves : (Listof Pos)]) #:transparent
define-type Play-Result play-result
struct play*-result-definitive ([turn : Side] [result : Play-Result]) #:transparent
struct play*-result-choice ([turn : Side] [lst : (Listof Play*-Result)]) #:transparent
struct play*-result-tbd ([board : Board] [side : Side] [rest-poss : (Listof Pos)] [rev-moves : (Listof Pos)]) #:transparent
define-type Play*-Result-Definitive play*-result-definitive
define-type Play*-Result-Choice play*-result-choice
define-type Play*-Result-TBD play*-result-tbd
define-type Play*-Result-MBD (U Play*-Result-Definitive Play*-Result-TBD)
define-type Play*-Result (U Play*-Result-MBD Play*-Result-Choice)

: play*-result-mbd? : Any -> Boolean : Play*-Result-MBD
define play*-result-mbd?(r)
  {play*-result-definitive?(r) or play*-result-tbd?(r)}

: play*-result? : Any -> Boolean : Play*-Result
define play*-result?(r)
  {play*-result-mbd?(r) or play*-result-choice?(r)}

: play*-result-turn : Play*-Result -> Side
define res.play*-result-turn
  case/type res
    Play*-Result-Definitive
      res.play*-result-definitive-turn
    Play*-Result-Choice
      res.play*-result-choice-turn
    Play*-Result-TBD
      res.play*-result-tbd-side

: play*-result-mbd-board : Play*-Result-MBD -> Board
define play*-result-mbd-board(res)
  case/type res
    Play*-Result-TBD
      res.play*-result-tbd-board
    Play*-Result-Definitive
      res.play*-result-definitive-board

: play*-result-definitive-winner : Play*-Result-Definitive -> (U Side #f)
define res.play*-result-definitive-winner
  res.play*-result-definitive-result.play-result-winner

: play*-result-definitive-board : Play*-Result-Definitive -> Board
define res.play*-result-definitive-board
  res.play*-result-definitive-result.play-result-board

: play*-result-turn=?/c : Side -> [Play*-Result -> Boolean]
define play*-result-turn=?/c(turn)(res)
  symbol=? res.play*-result-turn turn

: play*-result-definitive-winner=?/c : (U Side #f) -> [Play*-Result -> Boolean : #:+ Play*-Result-Definitive]
define play*-result-definitive-winner=?/c(side)(res)
  and
    play*-result-definitive? res
    equal? res.play*-result-definitive-winner side

: play*-result-combine : Play*-Result * -> Play*-Result
define (play*-result-combine . args)
  define-values (definative-results other-results)
    (inst partition Play-Result Play*-Result) play-result? args
  my-cond
    if empty?(definative-results)
      my-cond
        if empty?(other-results)
          ;play*-result-thunk-list 'X '()
          error 'play*-result-combine "expects at least one argument"
        else
          error 'dontknow
    else
      error 'dontknow

: play* : Play*-Result-TBD -> Play*-Result
define play*(arg)
  my-cond
    #:defs
      match-define play*-result-tbd(board side rest-poss rev-moves) arg
      define winner board-winner(board)
    if winner
      play*-result-definitive side
        play-result board winner reverse(rev-moves)
    else-if empty?(rest-poss)
      play*-result-definitive side
        play-result board #f reverse(rev-moves)
    #:defs
      define next-boards
        for/list ([pos in-list(rest-poss)]) : (Listof Board)
          hash-set board pos side
      define other side.other-side
      define-values [next-definitive-results tbds]
        for/fold ([def : (Listof Play*-Result-Definitive) '()]
                  [indef : (Listof Play*-Result-TBD) '()])
          ([p in-list(rest-poss)] [b in-list(next-boards)])
          my-cond
            #:defs
              define winner board-winner(b)
              define new-rest-poss rest-poss.rmv(p)
              define new-rev-moves cons(p rev-moves)
            if {winner or empty?(rest-poss)}
              values
                cons
                  play*-result-definitive side
                    play-result b winner reverse(new-rev-moves)
                  def
                indef
            else
              values
                def
                cons
                  play*-result-tbd(b other new-rest-poss new-rev-moves)
                  indef
      define win find-win(side next-definitive-results)
      define tbds* symetry-trim(tbds)
    if win
      win
    #:def
      define tie find-tie(next-definitive-results)
    if tie
      my-cond
        if empty?(tbds*)
          tie
        else
          play*-result-choice side
            cons
              tie
              tbds*
    else
      play*-result-choice side
        tbds*

: play*-result-down/no-trim : Play*-Result -> Play*-Result
define play*-result-down/no-trim(res)
  my-cond
    if play*-result-definitive?(res)
      res
    else-if play*-result-tbd?(res)
      play*-result-down/no-trim play*(res)
    #:def
      match-define play*-result-choice(side lst) res
    if empty?(lst)
      error 'play*-result-down/no-trim "WAT on line ~v" (quote-line-number)
    else-if empty?(lst.rest)
      define r lst.first
      play*-result-down/no-trim r
    #:defs
      define other side.other-side
      define next-results
        for/list ([r in-list(lst)]) : (Listof Play*-Result)
          my-cond
            if play*-result-tbd?(r)
              play*(r)
            else
              play*-result-down/no-trim r
      define next-results*
        trim-my-results(side next-results)
    if empty?(next-results*)
      error 'play*-result-down/no-trim "WAT on line ~v" (quote-line-number)
    else-if empty?(next-results*.rest)
      next-results*.first
    else
      play*-result-choice side
        next-results*

: find-win : Side (Listof Play*-Result) -> (U Play*-Result-Definitive #f)
define find-win(side results)
  my-cond
    #:def
      define wins
        filter
          (play*-result-definitive-winner=?/c side)
          results
    if not(empty?(wins))
      rnd-elt(wins)
    else
      #f

: find-tie : (Listof Play*-Result) -> (U Play*-Result-Definitive #f)
define find-tie(results)
  my-cond
    #:def
      define ties
        filter
          (play*-result-definitive-winner=?/c #f)
          results
    if not(empty?(ties))
      rnd-elt(ties)
    else
      #f

: trim-my-results : Side (Listof Play*-Result) -> (Listof Play*-Result)
define trim-my-results(side results)
  my-cond
    #:defs
      define-values [definative-results other-results]
        (inst partition play*-result-definitive Play*-Result) play*-result-definitive? results
      define win
        find-win(side definative-results)
    if win
      list[win]
    #:def
      define tie
        find-tie(definative-results)
    if tie
      cons tie
        other-results
    else-if not(empty?(other-results))
      other-results
    else-if not(empty?(definative-results))
      ;; It's a loss
      define losses definative-results
      list[rnd-elt(losses)]
    else
      error "WAT on line ~a" (quote-line-number)
      '()

: symetry-trim : (Listof Play*-Result) -> (Listof Play*-Result)
define symetry-trim(lst)
  my-cond
    if empty?(lst)
      '()
    #:def
      match-define (cons fst rst) lst
    else-if empty?(rst)
      list[fst]
    else-if play*-result-choice?(fst)
      cons fst
        symetry-trim(rst)
    #:defs
      define fst-bd
        fst.play*-result-mbd-board
      define fst-bd-cnt
        fst-bd.hash-count
      define fst-bds/t
        for/list ([t (in-list symetry-transforms)]) : (Listof Board)
          transform-board fst-bd t
      define-values [rst-like-fst rst*]
        partition
          λ (r)
            and
              play*-result-mbd?(r)
              let ([r-bd r.play*-result-mbd-board])
                and
                  equal? r-bd.hash-count fst-bd-cnt
                  for/or ([fst-bd (in-list fst-bds/t)]) : Boolean
                    equal? r-bd fst-bd
          rst
    else
      define fst-ish
        cons(fst rst-like-fst)
      cons
        rnd-elt(fst-ish)
        symetry-trim(rst*)

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



: play : Board Side -> Play-Result
define play(board side)
  define r
    play* play*-result-tbd(board side all-poss.rmv*(board.hash-keys) '())
  : process-r : Play*-Result -> Play-Result
  define process-r(r)
    my-cond
      if play*-result-definitive?(r)
        r.play*-result-definitive-result
      else
        process-r(play*-result-down/no-trim(r))
  process-r(r)

: best-move : Board Side -> Pos
define best-move(board side)
  define res play(board side)
  define moves res.play-result-moves
  my-cond
    if empty?(moves)
      error 'best-move "no move to make"
    else
      moves.first

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

: instant-replay : Play-Result -> Play-Result
define instant-replay(res)
  match-define play-result(final-board winner moves) res
  define init-board
    final-board.hsh-rmv*(moves)
  : start-side : Side
  define start-side
    my-cond
      if odd?(moves.length)
        (or winner 'X)
      else
        (or (and winner other-side(winner)) 'O)
  displayln "replay:"
  display-board init-board
  define-values (board side)
    for/fold ([board : Board init-board] [side : Side start-side]) ([pos (in-list moves)])
      define new-board
        hash-set board pos side
      displayln "~~~~~~~~~"
      display-board new-board
      values(new-board side.other-side)
  displayln "~~~~~~~~~"
  printf("winner: ~a\n" winner)
  unless (equal? board final-board)
    error 'instant-replay "something went wrong because the boards aren't equal"
  unless (equal? (and winner side.other-side) winner)
    error 'instant-replay "something went wrong because the winner isn't right"
  res

: spaces->board : (Listof (Listof (U Side #f))) -> Board
define spaces->board(spaces)
  unless {spaces.length = 3}
    error('spaces->board "bad")
  for/hash ([pos in-list(all-poss)]
            [spc in-list(append*(spaces))]
            #:when spc) : Board
    values(pos assert(spc))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

module* test racket/base
  require rackunit
          (submod "..")
          syntax/parse/define
          syntax/location
          racket/port
          for-syntax racket/base
                     syntax/parse
  begin-for-syntax
    define-syntax-class spc
      pattern (~literal X) #:with norm this-syntax
      pattern (~literal O) #:with norm this-syntax
      pattern (~literal _) #:with norm #'#f
  define-simple-macro
    BOARD
      a:spc ...
      ...
    spaces->board
      list
        list |a.norm| ...
        ...
  ;;
  check-equal? board-winner(hash()) #f
  check-equal?
    board-winner
      BOARD
        X X X
        _ _ _
        _ _ _
    X
  check-equal?
    board-winner
      BOARD
        X X O
        _ O _
        O X _
    O
  check-equal?
    board-winner
      BOARD
        X X O
        _ O O
        _ X _
    #f
  check-equal?
    board-winner
      BOARD
        O X X
        X X O
        O O X
    #f
  check-equal?
    BOARD
      O X X
      X X O
      O O X
    #hash([(0 0) . O] [(1 0) . X] [(2 0) . X]
          [(0 1) . X] [(1 1) . X] [(2 1) . O]
          [(0 2) . O] [(1 2) . O] [(2 2) . X]
          )
  check-equal?
    play
      BOARD
        X X _
        _ O _
        _ _ O
      'X
    play-result
      BOARD
        X X X
        _ O _
        _ _ O
      'X
      '((2 0))
  check-equal?
    play
      BOARD
        X _ _
        _ O _
        _ O X
      'X
    play-result
      BOARD
        X X O
        O O X
        X O X
      #f
      '((1 0) (2 0) (0 2) (0 1) (2 1))
  check-equal?
    length
      symetry-trim
        list
          play*-result-tbd
            BOARD
              X O _
              _ O _
              _ _ X
            X
            '()
            '()
          play*-result-tbd
            BOARD
              X _ _
              O O _
              _ _ X
            X
            '()
            '()
          play*-result-tbd
            BOARD
              X _ _
              _ O O
              _ _ X
            X
            '()
            '()
          play*-result-tbd
            BOARD
              X _ _
              _ O _
              _ O X
            X
            '()
            '()
          play*-result-tbd
            BOARD
              X _ O
              _ O _
              _ _ X
            X
            '()
            '()
          play*-result-tbd
            BOARD
              X _ _
              _ O _
              O _ X
            X
            '()
            '()
    2
  parameterize ([current-output-port (open-output-nowhere)])
    for ([i (in-range 50)])
      check board=?/symetry
        play-result-board
          play
            BOARD
              X _ _
              _ O _
              _ _ X
            O
        BOARD
          X O X
          X O O
          O X X
  instant-replay
    play
      hash()
      X


