#lang forge
// option solver MiniSatProver
// option core_minimization rce
// option logtranslation 1
// option coregranularity 1
option run_sterling "vis.js"

abstract sig Boolean {}
one sig True, False extends Boolean {}

abstract sig Orientation {}
one sig Horizontal, Vertical extends Orientation {}

fun MAX: one Int { 7 }

sig Coordinate {
  row: one Int,
  col: one Int
}

sig Ship {
  //replace with set of coordinates
  //note: values can be negative 
  locations: set Coordinate,
  orientation: one Orientation
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

//Returns the number of ships on the board
fun countShips[board: Board] : Int {
  #{ship: Ship | ship in board.ships}
}

//Returns the number of locations in a ship
fun countShipLocations[ship: Ship] : Int {
  #{loc: Coordinate | loc in ship.locations}
}

pred ship_wellformed[board: Board] {
  // All ship locations must be horizontal or vertical

  all s: board.ships | {
    s.orientation = Horizontal or s.orientation = Vertical
    s.orientation = Horizontal => {
      all loc1, loc2: s.locations | {
        loc1.row = loc2.row
        loc1.col != loc2.col
      }
    }
    s.orientation = Vertical => {
      all loc1, loc2: s.locations | {
        loc1.row != loc2.row
        loc1.col = loc2.col
      }
    }

    all loc1: s.locations | {
      some loc2: s.locations | {
        abs[loc1.row - loc2.row] <= 1 or abs[loc1.col - loc2.col] <= 1
      }
    }
    
  }
}

// Init state of the game - Rio
pred init[board: BoardState] {

  // Board needs to all be false
  all row, col: Int | row >= 0 and row <= MAX and col >= 0 and col <= MAX => {
    board.player1.shots[row][col] = False
    board.player2.shots[row][col] = False
  }
}

pred board_wellformed {
  // Board has to be 8x8
  // Player ships have to be 0-9
  all b: Board, r, c: Int | {
    some b.shots[r][c] => r >= 0 and r <= MAX and c >= 0 and c <= MAX
    
    all c: Coordinate | {
      c.row >= 0 and c.row <= MAX
      c.col >= 0 and c.col <= MAX
    }

    all s: b.ships | {
      #{loc: Coordinate | loc in s.locations} >= 1
      #{loc: Coordinate | loc in s.locations} <= 5

      
    }

    #{s: b.ships | s in b.ships} = 5
    all disj s1, s2: b.ships | {
      all loc1: s1.locations, loc2: s2.locations | {
        loc1.row != loc2.row or loc1.col != loc2.col
      }
    }

    one s: b.ships | countShipLocations[s] = 1
    one s: b.ships | countShipLocations[s] = 2
    one s: b.ships | countShipLocations[s] = 3
    one s: b.ships | countShipLocations[s] = 4
    one s: b.ships | countShipLocations[s] = 5
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
  // // Ship wellformed

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

// // If ship is hit in all positions it is sunk
// pred ship_sunk[board: Board, ship: Ship] {
//   // All positions of the ship are hit
//   all loc: ship.locations | {
//     board.shots[loc.row][loc.col] = True
//   }
// }

run {trace} for 15 Coordinate, 10 Ship, 5 BoardState for {next is linear}
