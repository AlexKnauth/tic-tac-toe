#lang postfix-dot-notation sweet-exp typed/racket/base

require racket/list
        my-cond/iffy
        "tic-tac-toe.rkt"

: read-move : (Listof Pos) -> Pos
define read-move(rest-poss)
  display "Enter a move: "
  define p
    read()
  my-cond
    if {(pos? p) and (member p rest-poss)}
      p
    else
      read-move(rest-poss)

: play-interactive* : Board Side (Listof Pos) -> Void
define play-interactive*(board human-side rest-poss)
  define computer-side other-side(human-side)
  : handle-winner : (U Side #f) -> Void
  define handle-winner(winner)
    my-cond
      if (equal? winner human-side)
        eprintf "Inconcievable!\n"
        displayln "You won!!!"
      else-if (equal? winner computer-side)
        displayln "You lost."
      else
        displayln "It's a tie."
  my-cond
    #:def
      define winner board.board-winner
    if winner
      handle-winner(winner)
      display-board board
    else-if empty?(rest-poss)
      handle-winner(#f)
      display-board board
    #:begin
      display-board board
      displayln "Your move:"
      define your-move
        read-move(rest-poss)
      define your-board
        hash-set board your-move human-side
      define winner your-board.board-winner
    if winner
      handle-winner(winner)
      display-board your-board
    #:def
      define your-rest-poss remove(your-move rest-poss)
    else-if empty?(your-rest-poss)
      handle-winner(#f)
      display-board your-board
    else
      display-board your-board
      displayln "Thinking..."
      define computer-move
        best-move(your-board computer-side)
      printf "Computer's move: ~a\n" computer-move
      define computer-board
        hash-set your-board computer-move computer-side
      play-interactive*(computer-board human-side remove(computer-move your-rest-poss))

: play-interactive : Board Side -> Void
define play-interactive(board human-side)
  play-interactive*(board human-side remove*(board.hash-keys all-poss))

play-interactive(hash() 'X)
