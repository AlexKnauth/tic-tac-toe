#lang postfix-dot-notation sweet-exp typed/racket/base

provide (all-defined-out)

require racket/match
        racket/bool
        typed/racket/class
        typed/racket/gui/base
        my-cond/iffy
        tic-tac-toe/tic-tac-toe

: make-Board : (HashTable Pos Side) -> Board
define make-Board(b) b

define-type Callback-Horizontal-Panel%
  Class
    #:implements/inits Horizontal-Panel%
    init
      callback [(Instance Window<%>) (Instance Mouse-Event%) -> Boolean]
: callback-horizontal-panel% : Callback-Horizontal-Panel%
define callback-horizontal-panel%
  class horizontal-panel%
    super-new()
    init
      callback : [(Instance Window<%>) (Instance Mouse-Event%) -> Boolean]
    : callback-function : [(Instance Window<%>) (Instance Mouse-Event%) -> Boolean]
    define callback-function callback
    define/override on-subwindow-event(receiver event)
      callback-function(receiver event)

define-type Cell%
  Class
    init
      parent (Instance Area-Container<%>)
      tic-tac-toe-object (Object [set-turn! [Side -> Void]])
      size Natural
      X (U 'human 'computer)
      O (U 'human 'computer)
    get-piece [-> (U Side #f)]
    add-piece! [Side -> Void]
    set-turn! [Side -> Void]
    game-over! [-> Void]
: cell% : Cell%
define cell%
  class object% super-new()
    init
      parent : (Instance Area-Container<%>)
      tic-tac-toe-object : (Object [set-turn! [Side -> Void]])
      size : Natural
      X : (U 'human 'computer)
      O : (U 'human 'computer)
    : h-panel : (Instance Callback-Horizontal-Panel%)
    define h-panel
      new callback-horizontal-panel%
        parent parent
        min-width size
        min-height size
        style '(border)
        alignment '(center center)
        callback
          λ (receiver event)
            on-subwindow-event(receiver event)
    : msg : (Instance Message%)
    define msg
      new message%
        label "  "
        parent h-panel
    : the-tic-tac-toe-object : (Object [set-turn! [Side -> Void]])
    define the-tic-tac-toe-object tic-tac-toe-object
    : X-human? : Boolean
    define X-human?
      equal? X 'human
    : O-human? : Boolean
    define O-human?
      equal? O 'human
    define/private on-subwindow-event([receiver : (Instance Window<%>)]
                                      [event : (Instance Mouse-Event%)]) : Boolean
      define human-turn?
        match turn
          'X X-human?
          'O O-human?
      my-cond
        if not(human-turn?)
          #f
        else-if (send event button-down? 'left)
          add-piece!(turn)
          #t
        else
          #f
    : piece : (U Side #f)
    define piece #f ; mutable
    define/public get-piece() : (U Side #f)
      piece
    define/public add-piece!([side : Side]) : Void
      when {not(game-over?) and not(piece)}
        unless (equal? side turn)
          error 'add-piece!-method-of-cell% "~a, it's not your turn!" side
        send msg set-label side.symbol->string
        set! piece side
        send the-tic-tac-toe-object set-turn! other-side(side)
    : turn : Side
    define turn 'X ; mutable
    define/public set-turn!([side : Side]) : Void
      set! turn side
    : game-over? : Boolean
    define game-over? #f ; mutable
    define/public game-over!() : Void
      set! game-over? #t

define tic-tac-toe%
  class object% super-new() inspect(#f)
    init
      parent : (Instance Area-Container<%>)
      cell-size : Natural
      X : (U 'human 'computer)
      O : (U 'human 'computer)
    : X-human? : Boolean
    define X-human?
      equal? X 'human
    : O-human? : Boolean
    define O-human?
      equal? O 'human
    : v-panel : (Instance Vertical-Panel%)
    define v-panel
      new vertical-panel%
        parent parent
        stretchable-width #f
        stretchable-height #f
    : msg : (Instance Message%)
    define msg
      new message%
        label "      Your move      "
        parent v-panel
    : h-panels : (Listof (Instance Horizontal-Panel%))
    define h-panels
      for/list ([y (in-range 3)]) : (Listof (Instance Horizontal-Panel%))
        new horizontal-panel%
          parent v-panel
          stretchable-width #f
          stretchable-height #f
    : cell-msgss : (Listof (Listof (Instance Cell%)))
    define cell-msgss
      for/list ([h-panel (in-list h-panels)]) : (Listof (Listof (Instance Cell%)))
        for/list ([x (in-range 3)]) : (Listof (Instance Cell%))
          new cell%
            parent h-panel
            tic-tac-toe-object this
            size cell-size
            X X
            O O
    : cell-msg-hsh : (HashTable Pos (Instance Cell%))
    define cell-msg-hsh
      for/fold
        ([hsh : (HashTable Pos (Instance Cell%)) #hash()])
        ([y (in-range 3)] [cell-msg-row (in-list cell-msgss)])
        for/fold
          ([hsh : (HashTable Pos (Instance Cell%)) hsh])
          ([x (in-range 3)] [cell-msg (in-list cell-msg-row)])
          hash-set hsh
            assert list(x y) pos?
            cell-msg
    define/public get-current-board() : Board
      for/fold ([board : Board (make-Board #hash())])
        ([([pos : Pos] [cell : (Instance Cell%)]) (in-hash cell-msg-hsh)])
        define piece
          send cell get-piece
        my-cond
          if piece
            make-Board
              hash-set board pos piece
          else
            board
    define/public game-over!() : Void
      for ([(pos cell) (in-hash cell-msg-hsh)])
        send cell game-over!
    define/public set-turn!([side : Side]) : Void
      for ([(pos cell) (in-hash cell-msg-hsh)])
        send cell set-turn! side
      define side-human?
        match side
          'X X-human?
          'O O-human?
      my-cond
        if side-human?
          void()
        #:begin
          when not{X-human? or O-human?}
            sleep 1
          define board get-current-board()
          define winner board.board-winner
        if winner
          game-over!()
          send msg set-label
            format "~a won!" winner
        else-if board-full?(board)
          send msg set-label "It's a tie."
        #:begin
          send msg set-label "thinking..."
          define next-move best-move(board side)
          define cell hash-ref(cell-msg-hsh next-move)
          send cell add-piece! side
          define next-board get-current-board()
          define next-winner next-board.board-winner
        if next-winner
          game-over!()
          send msg set-label
            format "~a won!" next-winner
        else-if board-full?(board)
          send msg set-label "It's a tie."
        else
          send msg set-label "Your Move:"
          


