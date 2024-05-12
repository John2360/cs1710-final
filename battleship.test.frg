#lang forge

open "battleship.frg"  


//shots outside of range 
pred badBoard_shots {
  some board: Board | {
    some row, col: Int | {
      (row < 0 or row > 7 or col < 0 or col > 7) and board.shots[row][col] = True
    }
  }
}

//ships outside of range 
pred badBoard_ships {
  some board: Board | {
    some s: board.ships| {
      some loc:s.locations|{
        loc.row < 0 or loc.row > 7 or loc.col < 0 or loc.col > 7
        loc.row = True 
        loc.col = True}
    }
  }
}

//no boards or ships on board
pred empty_board {
  all board: Board|{
    all row, col: Int | row >= 0 and row <= MAX and col >= 0 and col <= MAX => {
      board.shots[row][col] = False
    }
    no board.ships
  }
}

// All positions within board range are filled with shots
pred all_shots_in_range {
  all board: Board, row, col: Int | {
    (row >= 0 and row <= 7 and col >= 0 and col <= 7) implies board.shots[row][col] = True
  }
}


// Ensures that no ships overlap
pred no_overlap_ships {
  all board: Board | {
    all disj s1, s2: board.ships | {
      no loc1: s1.locations, loc2: s2.locations | loc1 = loc2
    }
  }
}


// Ensures the ships are well-formed
test suite for ship_wellformed {
  test expect {
    badPlacement : { all board : Board | badBoard_ships } is unsat
    allShipsWellFormed : { all board : Board | ship_wellformed[board] } is sat
    noOverlap : {no_overlap_ships} is sat
  }
}

fun countShipLocations[ship: Ship] : Int {
  #{loc: Coordinate | loc in ship.locations}
}

// all ships are of correct size
pred correctShipSizes[board: Board] {
  all s: board.ships | {
    // accounting for init board
    let size = countShipLocations[s] | size >= 0 and size <= 5
  }
}

test suite for correctShipSizes {
  test expect {
    validShipSizes: { all board: Board | correctShipSizes[board] } is sat
    oversizedShips: { some board: Board | not correctShipSizes[board] } is unsat
  }
}

pred not_board_wellformed { not board_wellformed}

// Ensures board is wellformed 
test suite for board_wellformed {
    assert empty_board is necessary for board_wellformed
    assert all_shots_in_range is necessary for board_wellformed
}

test suite for not_board_wellformed {
    assert badBoard_shots is sufficient for not_board_wellformed
    assert badBoard_ships is sufficient for not_board_wellformed
}

// it should be possible for all positions to have been shot at
pred fullBoardShots[board: Board] {
  all row, col: Int | (row >= 0 and row <= MAX and col >= 0 and col <= MAX) => board.shots[row][col] = True
}

test suite for fullBoardShots {
  test expect {
    completeCoverage: { all board: Board | fullBoardShots[board] } is sat
    incompleteCoverage: { some board: Board | not fullBoardShots[board] } is sat
  }
}

// Tests for the initialization state of the game
pred bad_init_boardstate[b: BoardState] {
  some row, col: Int | {
    (row >= 0 and col >= 0 and row <= MAX and col <= MAX)
    (b.player1.shots[row][col] = True or b.player2.shots[row][col] = True)
  }
}

// Both players have taken same number of shots
pred boardStateWithEvenNumberShots[b: BoardState] {
  countShots[b.player1] = countShots[b.player2]
}

// Player 1 has taken one more shot than player 2
pred boardStateWithOneMoreShot[b: BoardState] {
  countShots[b.player1] = countShots[b.player2] + 1
}

// Test that game is initialized correctly
test suite for init {
  test expect {
    // initialEmpty : { all b: BoardState | init[b] and empty_board} is sat
    // badInit : { all b: BoardState | bad_init_boardstate[b] } is sat
  }
}

// Checks for player 1's turn properly
test suite for player1Turn {
  test expect {
    evenShotsLeadToPlayer1Turn : { all b: BoardState | boardStateWithEvenNumberShots[b] implies player1Turn[b] } is sat
  }
}

// Checks for player 2's turn properly
test suite for player2Turn {
  test expect {
    oddShotsLeadToPlayer2Turn : { all b: BoardState | boardStateWithOneMoreShot[b] implies player2Turn[b] } is sat
  }
}

// Tests for the mechanics of a move in the game
pred onlyOneShot[pre, post: BoardState]{
  add[countShots[pre.player1], countShots[pre.player2]] = subtract[add[countShots[post.player1], countShots[post.player2]], 1]
}


pred player1IsSame[pre, post: BoardState]{
  pre.player1 = post.player1
}

pred player2IsSame[pre, post: BoardState]{
  pre.player2 = post.player2
}


test suite for move {
    test expect {
      takesOnlyOneShot: {all b: BoardState | {
        (player1Turn[b] or player2Turn[b])
          some Game.next[b] => {
            some row, col: Int | {
              move[b, Game.next[b], row, col]
              and onlyOneShot[b, Game.next[b]]

              player1Turn[b] => player2IsSame[b, Game.next[b]]
              player2Turn[b] => player1IsSame[b, Game.next[b]]
            } 
          }
        }
      } is sat

      possibleInvalidTurn: {all b: BoardState | {
        (player1Turn[Game.next[b]] and player2Turn[Game.next[b]])
          some Game.next[b] => {
            some row, col: Int | {
              move[b, Game.next[b], row, col]
              and onlyOneShot[b, Game.next[b]]
            } 
          }
        }
      } is unsat

      validMoveAtEdge: {
        all b: BoardState | {
          (player1Turn[b] or player2Turn[b])
          some Game.next[b] => {
            some row, col: Int | {
              (row = 0 or row = MAX or col = 0 or col = MAX) and
              move[b, Game.next[b], row, col] and
              onlyOneShot[b, Game.next[b]]
            }
          }
        }
      } is sat

      noMoveWhenNotTurn: {
        all b: BoardState | {
          (not player1Turn[b] and not player2Turn[b])
          some Game.next[b] => {
            all row, col: Int | {
              not move[b, Game.next[b], row, col]
            }
          }
        }
      } is sat

      
      noRepeatedShots: {
        all b: BoardState | {
          (player1Turn[b] or player2Turn[b])
          some Game.next[b] => {
            some row, col: Int | {
              (player1Turn[b] => b.player1.shots[row][col] = False and move[b, Game.next[b], row, col])
              (player2Turn[b] => b.player2.shots[row][col] = False and move[b, Game.next[b], row, col])
            }
          } 
        }        
      } is sat
  }
}