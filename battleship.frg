#lang forge
option solver MiniSatProver
option core_minimization rce
option logtranslation 1
option coregranularity 1
option run_sterling "vis.js"

abstract sig Boolean {}
one sig True, False extends Boolean {}

abstract sig Orientation {}
one sig Horizontal, Vertical extends Orientation {}

fun MAX: one Int { 7 }
fun DIFF_BOARDS: one Boolean { True }

fun cells: set Int {
    0 + 1 + 2 + 3 + 4 + 5 + 6 + 7
}

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

// pred ship_wellformed[board: Board] {
//   all s: board.ships | {
//     s.orientation = Horizontal or s.orientation = Vertical
    
//     s.orientation = Horizontal => {
//       all loc1: s.locations | {
//         all loc2: s.locations - loc1 | {
//           loc1.row = loc2.row and 
//           (loc1.col + 1 = loc2.col or loc1.col - 1 = loc2.col)
//         }
//       }
//     }

//     s.orientation = Vertical => {
//       all loc1: s.locations | {
//         all loc2: s.locations - loc1 | {
//           loc1.col = loc2.col and 
//           (loc1.row + 1 = loc2.row or loc1.row - 1 = loc2.row)
//         }
//       }
//     }
//   }
// }

// pred ship_wellformed[board: Board] {
//   // All ship locations must be horizontal or vertical

//   all s: board.ships | {
//     // Ships are in a line
//     s.orientation = Vertical or s.orientation = Horizontal
    
//     // TODO: Fix this stuff
//     s.orientation = Vertical => {
//       let rows = s.locations.row | {
//         #{rows} = 1
//         all c1: s.locations | some c2: s.locations - c1 | {
//           c1.col = add[c2.col, 1] or c1.col = add[c2.col, -1]
//         }
//       }
//     }

//     s.orientation = Horizontal => {
//       let cols = s.locations.col | {
//         #{cols} = 1
//         all c1: s.locations | some c2: s.locations - c1 | {
//           c1.row = add[c2.row, 1] or c1.row = add[c2.row, -1]
//         }
//       }
//     }
//   }
// }

pred ship_wellformed[board: Board] {
  all s: board.ships | {
    s.orientation = Horizontal or s.orientation = Vertical
    (
      s.orientation = Horizontal => {
        // Comment line out below to allow for sat
        all row1: s.locations | all row2: s.locations | row1 = row2
        all c1, c2: s.locations | c1.row = c2.row => (c1.col + 1 = c2.col or c1.col - 1 = c2.col)
      }
    ) and (
      s.orientation = Vertical => {
        // Comment line out below to allow for sat
        all col2: s.locations | all col2: s.locations | col2 = col2
        all c1, c2: s.locations | c1.col = c2.col implies
        (c1.row + 1 = c2.row or c1.row - 1 = c2.row)
      }
    )
  }
  #{s: board.ships | countShipLocations[s] = 1} = 1
  #{s: board.ships | countShipLocations[s] = 2} = 1
  #{s: board.ships | countShipLocations[s] = 3} = 1
  #{s: board.ships | countShipLocations[s] = 4} = 1
  #{s: board.ships | countShipLocations[s] = 5} = 1
}

// Init state of the game - Rio
pred init[board: BoardState] {

  // Board needs to all be false
  all row, col: cells | row >= 0 and row <= MAX and col >= 0 and col <= MAX => {
    board.player1.shots[row][col] = False
    board.player2.shots[row][col] = False
  }

  ship_wellformed[board.player1]
  ship_wellformed[board.player2]
}

pred board_wellformed {
  // Board has to be 8x8
  // Player ships have to be 0-9
  all b: Board, r, c: cells | {
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

  // Not all player 1 and player 2 ships are in the same space
  DIFF_BOARDS = True => {
    all b: BoardState | {
      // some s1: b.player1.ships, s2: b.player2.ships | {
      //   some loc1: s1.locations, loc2: s2.locations | {
      //     loc1.row != loc2.row or loc1.col != loc2.col
      //   }
      // }

      all s1: b.player1.ships | all s2: b.player2.ships | {
        s1 != s2
      }
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
    all row1, col1: cells | {
      (row1 != row or col1 != col) =>
      pre.player1.shots[row1][col1] = post.player1.shots[row1][col1]
    }

    all row1, col1: cells | {
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
    all row1, col1: cells | {
      (row1 != row or col1 != col) =>
      pre.player2.shots[row1][col1] = post.player2.shots[row1][col1]
    }

    all row1, col1: cells | {
      pre.player1.shots[row1][col1] = post.player1.shots[row1][col1]
    }
  }

  // All ships must stay in same position
  all s: pre.player1.ships | {
    s.locations & post.player1.ships.locations = s.locations
  }

  all s: pre.player2.ships | {
    s.locations & post.player2.ships.locations = s.locations
  }
}

inst optimizer {
    Orientation = `Horizontal0 + `Vertical0
    Horizontal = `Horizontal0
    Vertical = `Vertical0
    Coordinate = `Coordinate0 + `Coordinate1 + `Coordinate2 + `Coordinate3 + `Coordinate4 + `Coordinate5 + `Coordinate6 + `Coordinate7 +`Coordinate8  + `Coordinate9  + `Coordinate10 + `Coordinate11  + `Coordinate12  + `Coordinate13 + `Coordinate14
    
    // Ship 1
    `Coordinate0.row = 0
    `Coordinate0.col = 0

    // Ship 2
    `Coordinate1.row = 1
    `Coordinate1.col = 0

    `Coordinate2.row = 1
    `Coordinate2.col = 1

    // Ship 3
    `Coordinate3.row = 2
    `Coordinate3.col = 0

    `Coordinate4.row = 2
    `Coordinate4.col = 1

    `Coordinate5.row = 2
    `Coordinate5.col = 2

    // Ship 4
    `Coordinate6.row = 3
    `Coordinate6.col = 0

    `Coordinate7.row = 3
    `Coordinate7.col = 1

    `Coordinate8.row = 3
    `Coordinate8.col = 2

    `Coordinate9.row = 3
    `Coordinate9.col = 3

    // Ship 5
    `Coordinate10.row = 4
    `Coordinate10.col = 0

    `Coordinate11.row = 4
    `Coordinate11.col = 1

    `Coordinate12.row = 4
    `Coordinate12.col = 2

    `Coordinate13.row = 4
    `Coordinate13.col = 3

    `Coordinate14.row = 4
    `Coordinate14.col = 4

    Ship = `Ship0 + `Ship1 + `Ship2 + `Ship3 + `Ship4 + `Ship5
    
    `Ship0.locations = ( `Coordinate0 )
    `Ship0.orientation = `Horizontal0

    `Ship1.locations = ( `Coordinate1 + `Coordinate2 )
    `Ship1.orientation = `Vertical0

    `Ship2.locations = ( `Coordinate3 + `Coordinate4 + `Coordinate5 )
    `Ship2.orientation = `Vertical0

    `Ship3.locations = ( `Coordinate6 + `Coordinate7 + `Coordinate8 + `Coordinate9 )
    `Ship3.orientation = `Vertical0

    `Ship4.locations = ( `Coordinate10 + `Coordinate11 + `Coordinate12 + `Coordinate13 + `Coordinate14 )
    `Ship4.orientation = `Vertical0
}

inst optimizer2 {
    Orientation = `Horizontal0 + `Vertical0
    Horizontal = `Horizontal0
    Vertical = `Vertical0
    Coordinate = `Coordinate0 + `Coordinate1 + `Coordinate2 + `Coordinate3 + `Coordinate4 + `Coordinate5 + `Coordinate6 + `Coordinate7 +`Coordinate8  + `Coordinate9  + `Coordinate10 + `Coordinate11  + `Coordinate12  + `Coordinate13 + `Coordinate14 + `Coordinate15 + `Coordinate16 + `Coordinate17 + `Coordinate18 + `Coordinate19 + `Coordinate20 + `Coordinate21 + `Coordinate22 + `Coordinate23 + `Coordinate24 + `Coordinate25 + `Coordinate26 + `Coordinate27 + `Coordinate28 + `Coordinate29
    
    // Ship 1
    `Coordinate0.row = 0
    `Coordinate0.col = 0

    // Ship 2
    `Coordinate1.row = 0
    `Coordinate1.col = 1

    `Coordinate2.row = 1
    `Coordinate2.col = 1

    // Ship 3
    `Coordinate3.row = 0
    `Coordinate3.col = 2

    `Coordinate4.row = 1
    `Coordinate4.col = 2

    `Coordinate5.row = 2
    `Coordinate5.col = 2

    // Ship 4
    `Coordinate6.row = 0
    `Coordinate6.col = 3

    `Coordinate7.row = 1
    `Coordinate7.col = 3

    `Coordinate8.row = 2
    `Coordinate8.col = 3

    `Coordinate9.row = 3
    `Coordinate9.col = 3

    // Ship 5
    `Coordinate10.row = 0
    `Coordinate10.col = 4

    `Coordinate11.row = 1
    `Coordinate11.col = 4

    `Coordinate12.row = 2
    `Coordinate12.col = 4

    `Coordinate13.row = 3
    `Coordinate13.col = 4

    `Coordinate14.row = 4
    `Coordinate14.col = 4

    Ship = `Ship0 + `Ship1 + `Ship2 + `Ship3 + `Ship4 + `Ship5 + `Ship6 + `Ship7 + `Ship8 + `Ship9
    
    `Ship0.locations = ( `Coordinate0 )
    `Ship0.orientation = `Horizontal0

    `Ship1.locations = ( `Coordinate1 + `Coordinate2 )
    `Ship1.orientation = `Horizontal0

    `Ship2.locations = ( `Coordinate3 + `Coordinate4 + `Coordinate5 )
    `Ship2.orientation = `Horizontal0

    `Ship3.locations = ( `Coordinate6 + `Coordinate7 + `Coordinate8 + `Coordinate9 )
    `Ship3.orientation = `Horizontal0

    `Ship4.locations = ( `Coordinate10 + `Coordinate11 + `Coordinate12 + `Coordinate13 + `Coordinate14 )
    `Ship4.orientation = `Horizontal0
}

// ships of both horizontal and vertical orientations
inst optimizer3 {
    Orientation = `Horizontal0 + `Vertical0
    Horizontal = `Horizontal0
    Vertical = `Vertical0
    Coordinate = `Coordinate0 + `Coordinate1 + `Coordinate2 + `Coordinate3 + `Coordinate4 + `Coordinate5 + `Coordinate6 + `Coordinate7 +`Coordinate8  + `Coordinate9  + `Coordinate10 + `Coordinate11  + `Coordinate12  + `Coordinate13 + `Coordinate14
    
    // Ship 1 
    `Coordinate0.row = 0
    `Coordinate0.col = 0

    // Ship 2
    `Coordinate1.row = 0
    `Coordinate1.col = 1

    `Coordinate2.row = 1
    `Coordinate2.col = 1

    // Ship 3
    `Coordinate3.row = 3
    `Coordinate3.col = 0

    `Coordinate4.row = 3
    `Coordinate4.col = 1

    `Coordinate5.row = 3
    `Coordinate5.col = 2

    // Ship 4
    `Coordinate6.row = 1
    `Coordinate6.col = 5

    `Coordinate7.row = 2
    `Coordinate7.col = 5

    `Coordinate8.row = 3
    `Coordinate8.col = 5

    `Coordinate9.row = 4
    `Coordinate9.col = 5

    // Ship 5
    `Coordinate10.row = 5
    `Coordinate10.col = 0

    `Coordinate11.row = 5
    `Coordinate11.col = 1

    `Coordinate12.row = 5
    `Coordinate12.col = 2

    `Coordinate13.row = 5
    `Coordinate13.col = 3

    `Coordinate14.row = 5
    `Coordinate14.col = 4

    Ship = `Ship0 + `Ship1 + `Ship2 + `Ship3 + `Ship4 + `Ship5
    
    `Ship0.locations = ( `Coordinate0 )
    `Ship0.orientation = `Horizontal0

    `Ship1.locations = ( `Coordinate1 + `Coordinate2 )
    `Ship1.orientation = `Horizontal0

    `Ship2.locations = ( `Coordinate3 + `Coordinate4 + `Coordinate5 )
    `Ship2.orientation = `Vertical0

    `Ship3.locations = ( `Coordinate6 + `Coordinate7 + `Coordinate8 + `Coordinate9 )
    `Ship3.orientation = `Horizontal0

    `Ship4.locations = ( `Coordinate10 + `Coordinate11 + `Coordinate12 + `Coordinate13 + `Coordinate14 )
    `Ship4.orientation = `Vertical0
}


pred trace {
  // Init
  init[Game.first]
  // Board wellformed
  board_wellformed
  // Ship wellformed
  ship_wellformed[Game.first.player1]
  ship_wellformed[Game.first.player2]


  // Move
  all b: BoardState | { 
    some Game.next[b] => {
      some row, col: cells | {
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

// run {trace} for 15 Coordinate, 5 Ship, 1 BoardState for {next is linear}
run {trace} for 1 BoardState for {optimizer2}
