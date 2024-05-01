#lang forge/bsl
// option solver MiniSatProver
// option core_minimization rce
// option logtranslation 1
// option coregranularity 1

option run_sterling "vis.js"

abstract sig Boolean {}
one sig True, False extends Boolean {}

abstract sig Orientation {}
one sig Horizontal, Vertical extends Orientation {}

//expensive to keep info in two places -- startrow, startcol and board.ships
sig Ship {
  //replace with set of coordinates
  //note: values can be negative 
  startRow: one Int,
  startCol: one Int,
  orientation: one Orientation,
  length: one Int
}

//Contains info on positions of ships and shots
sig Board {
  shots: pfunc Int -> Int -> Boolean,
  ships: pfunc Int -> Int -> Ship
}

//keeps track of order of boards
one sig Game {
  first: one BoardState,
  next: pfunc BoardState -> BoardState
}

//Used in Game, contains two player Boards
sig BoardState {
  player1: one Board,
  player2: one Board
}

//Returns the number of shots on the board
fun countShots[board: Board] : Int {
  #{row, col: Int | board.shots[row][col] = True}
}

//Returns number of ships placed on board
fun countShips[board: Board] : Int {
  #{row, col: Int | some board.ships[row][col]}
}

//Ensures the number of ships on the board is equal to 5
pred ship_wellformed[board: Board] {
  all row, col: Int | {
    all ship: board.ships[row][col] | {
      ship.startRow >= 0 and ship.startRow <= MAX and
      ship.startCol >= 0 and ship.startCol <= MAX and
      (ship.orientation = Horizontal => (add[ship.startCol, ship.length]) <= MAX) and
      (ship.orientation = Vertical => (add[ship.startRow, ship.length]) <= MAX)
    }
  }
  countShips[board] = 5
}


// pred ship_wellformed[board: Board] {
//   countShips[board] = 5
// }

// Init state of the game - Rio
pred init[board: BoardState] {

  // Board needs to all be false
  all row, col: Int | {
    (row >= 0 and row <= MAX and col >= 0 and col <= MAX) implies board.player1.shots[row][col] = False
    (row >= 0 and row <= MAX and col >= 0 and col <= MAX) implies board.player2.shots[row][col] = False
  }

  ship_wellformed[board.player1]
  ship_wellformed[board.player2]
}

fun MAX: one Int { 7 }


pred board_wellformed {
  // Player shots have to be 0-9
  // Player ships have to be 0-9
  all row, col: Int, board: Board | {
    board.shots[row][col] = True implies row >= 0 and row <= MAX and col >= 0 and col <= MAX
    board.shots[row][col] != True implies board.shots[row][col] = False
    board.ships[row][col] = True implies row >= 0 and row <= MAX and col >= 0 and col <= MAX
  }

  // Player ships are consistent across board states
  all b1, b2: BoardState | {
    all row, col: Int | {
      b1.player1.ships[row][col] = b2.player1.ships[row][col]
      b1.player2.ships[row][col] = b2.player2.ships[row][col]
    }
  }

}

//Checks if it is player1's turn
pred player1Turn[b: BoardState] {
  countShots[b.player1] = countShots[b.player2]
}

//Checks if it is player2's turn
pred player2Turn[b: BoardState] {
  countShots[b.player1] = add[countShots[b.player2], 1]
}

pred balancedTurns[b: BoardState] {
  player1Turn[b] or player2Turn[b]
}


pred move[pre, post: BoardState, row, col: Int] {
  // Check if the position has already been shot at
  balancedTurns[pre]
  //If it is player1's turn
  player1Turn[pre] => {
    //The position in pre hasn't been shot at yet
    pre.player1.shots[row][col] = False
    //The position in post has to have been shot at
    post.player1.shots[row][col] = True

    //All positions that aren't the changed one stay the same
    all row1, col1: Int | {
      (row1 != row or col1 != col) =>
      pre.player1.shots[row1][col1] = post.player1.shots[row1][col1]
    }

    all row1, col1: Int | {
      pre.player2.shots[row1][col1] = post.player2.shots[row1][col1]
    }
  }
  //If it is player2's turn
  player2Turn[pre] => {
    //The position in pre hasn't been shot at yet
    pre.player2.shots[row][col] = False
    //The position in post has to have been shot at
    post.player2.shots[row][col] = True

    //All positions that aren't the changed one stay the same
    all row1, col1: Int | {
      (row1 != row or col1 != col) =>
      pre.player2.shots[row1][col1] = post.player2.shots[row1][col1]
    }

    all row1, col1: Int | {
      pre.player1.shots[row1][col1] = post.player1.shots[row1][col1]
    }
  }
}

/** WIN CONDITIONS ***************************/
pred ship_sunk[ship: Ship, board: Board] {
  all pos: Int | {
    // because we start indexing from 0
    (pos < ship.length) implies (
      (ship.orientation = Horizontal and board.shots[ship.startRow][ship.startCol + pos] = True) or
      (ship.orientation = Vertical and board.shots[ship.startRow + pos][ship.startCol] = True)
    )
  }
}

pred player_wins[player_board: Board, opponent_board: Board] {
  all ship: opponent_board.ships | ship_sunk[ship, player_board]
}





/** GAME STATE ******************************/ 
pred trace {
  // Init
  init[Game.first]
  // Board wellformed
  board_wellformed
  // Ship wellformed

  // Move
  all b: BoardState | { 
    some Game.next[b] => {
      some row, col: Int | {
        move[b, Game.next[b], row, col]
      } 
    }
  }
  // Check for win and keep same if won
}

run {trace} for 5 BoardState for {next is linear}
