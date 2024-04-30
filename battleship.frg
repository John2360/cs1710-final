#lang forge
// option solver MiniSatProver
// option core_minimization rce
// option logtranslation 1
// option coregranularity 1

option run_sterling "vis.js"

abstract sig Boolean {}
one sig True, False extends Boolean {}

sig Coordinate {
  row: one Int,
  col: one Int
}

//expensive to keep info in two places -- startrow, startcol and board.ships
sig Ship {
  //replace with set of coordinates
  //note: values can be negative 
  locations: set Coordinate
}

//Contains info on positions of ships and shots
sig Board {
  shots: pfunc Int -> Int -> Boolean,
  ships: set Ship
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
  #{ship: Ship | ship in board.ships}
}

fun countShipLocations[ship: Ship] : Int {
  #{loc: Coordinate | loc in ship.locations}
}

// If ship is hit in all positions it is sunk
pred ship_sunk[board: Board, ship: Ship] {
  // All positions of the ship are hit
  all loc: ship.locations | {
    board.shots[loc.row][loc.col] = True
  }
}

//Ensures the number of ships on the board is equal to 5
pred ship_wellformed[board: Board] {
  // Only can put 4 ships on the board???
  countShips[board] = 4
  
  // Why doesent this work??
  // some ship: Ship | countShipLocations[ship] = 5
  // some ship: Ship | countShipLocations[ship] = 4
  // some ship: Ship | countShipLocations[ship] = 3
  // some ship: Ship | countShipLocations[ship] = 2


  // No ships overlap
  all s1, s2: board.ships | {
    s1 != s2 implies no s1.locations & s2.locations
  }

  // Ships are in bounds
  all ship: board.ships | {
    all loc: ship.locations | {
      loc.row >= 0 and loc.row <= MAX
      loc.col >= 0 and loc.col <= MAX
    }
  }

  // Ships are contiguous
  all ship: board.ships | {
    all loc1, loc2: ship.locations | {
      (loc1.row = loc2.row and abs[loc1.col - loc2.col] = 1) or
      (loc1.col = loc2.col and abs[loc1.row - loc2.row] = 1)
    }
  }

  // Ships are not diagonal
  all ship: board.ships | {
    all loc1, loc2: ship.locations | {
      loc1.row = loc2.row or loc1.col = loc2.col
    }
  }

}

// Init state of the game - Rio
pred init[board: BoardState] {

  // Board needs to all be false
  all row, col: Int | {
    (row >= 0 and row <= MAX and col >= 0 and col <= MAX) implies board.player1.shots[row][col] = False
    (row >= 0 and row <= MAX and col >= 0 and col <= MAX) implies board.player2.shots[row][col] = False
  }

  // Board needs to have 5 ships
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
