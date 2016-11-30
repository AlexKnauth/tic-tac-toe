#lang postfix-dot-notation sweet-exp typed/racket/base

require typed/racket/class
        typed/racket/gui/base
        tic-tac-toe/tic-tac-toe
        "gui.rkt"

define frame
  new frame%
    label "the frame"
    width 300
    height 300

define board
  new tic-tac-toe%
    parent frame
    cell-size 100
    X 'human
    O 'computer

send frame show #t

