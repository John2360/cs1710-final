#lang forge/bsl

open "battleship.frg"

//shots outside of range 
pred badBoard_shots{
  some board: Board | {
    some row, col: Int | {
      row < 0 or
      col < 0 or
      row > 7 or
      row > 7
      board.shots[row][col] = True
    }
  }
}

//ships outside of range 
pred badBoard_ships{
  some board: Board | {
    some row, col: Int | {
      row < 0 or
      col < 0 or
      row > 7 or
      row > 7
      board.ships[row][col] = True
    }
  }
}

//All positions are empty
pred empty_board{
  all board: Board, row, col: Int | {
    board.shots[row][col] = False
    board.ships[row][col] = False
  }
}

//Everything in range is true
pred all_true_inrange{
  all board: Board, row, col: Int | {
    (row < 0 or col < 0 or row > 7 or col > 7) implies board.shots[row][col] = False
    (row < 0 or col < 0 or row > 7 or col > 7) implies board.ships[row][col] = False
    (row >= 0 and col >= 0 and row <= 7 and col <= 7) implies board.shots[row][col] = True 
    (row >= 0 and col >= 0 and row <= 7 and col <= 7) implies board.ships[row][col] = True
  }
}

pred not_board_wellformed { not board_wellformed}

test suite for board_wellformed {

    assert badBoard_shots is sufficient for not_board_wellformed
    assert badBoard_ships is sufficient for not_board_wellformed
    assert empty_board is sufficient for board_wellformed
    assert all_true_inrange is sufficient for board_wellformed
}

//No ships on board
pred no_ships[board:Board]{
  all row, col : Int | {
    board.ships[row][col] = False
  }
}

//Every postion contains a ship
pred too_many_ships[board: Board]{
  all row, col : Int | {
    board.ships[row][col] = True
  }
}

//There are exactly five ships on the board
pred five_ships[board: Board]{
  all row, col : Int | {
    ((row = 0 and col = 0) or 
    (row = 0 and col = 1) or 
    (row = 0 and col = 2) or 
    (row = 1 and col = 0) or 
    (row = 1 and col = 1) ) implies board.ships[row][col] = True else board.ships[row][col] = False
  }
}

test suite for ship_wellformed {
    test expect {
      noShips : { (all board : Board | no_ships[board] and ship_wellformed[board] )} is unsat
      tooManyShips : { (all board : Board | too_many_ships[board] and ship_wellformed[board] )} is unsat
      fiveShips : { (all board : Board | five_ships[board] and ship_wellformed[board] )} is sat
    }
}

//The board contains at least one shot 
pred board_contains_shot[board: Board] {
  some row, col: Int | {
    (row >= 0 and col >= 0 and row <= 7 and col <= 7)
    board.shots[row][col] = True
  }
}

//Some board in boardstate contains a shot
pred bad_init_boardstate[b: BoardState]{
  board_contains_shot[b.player1] or
  board_contains_shot[b.player2]
}

//One of the boards doesn't have exactly 5 ships
pred ship_badlyformed_boardstate[b: BoardState]{
  not ship_wellformed[b.player1] or
  not ship_wellformed[b.player2]
}

test suite for init {
    
    test expect {
      containsShot : { (all boardState : BoardState | bad_init_boardstate[boardState] and init[boardState] )} is unsat
      badShips : { (all boardState : BoardState | ship_badlyformed_boardstate[boardState] and init[boardState] )} is unsat
    }
}

//Both boards have same number of shots
pred boardStateWithEvenNumberShots[board: Board]{
  some numShots: Int | {
    countShots[board.player1] = numShots
    and countShots[board.player2] = numShots
  }
}

//Player1 has one more shot on their board
pred boardStateWithOneMoreShot[board: BoardState]{
  some numShots: Int | {
    countShots[board.player1] = numShots
    and countShots[board.player2] = subtract[numShots, 1]
  }
}

test suite for player1Turn {
    test expect {
      boardWithEvenNumberShots : { (all board : BoardState | boardStateWithEvenNumberShots[board] and player1Turn[board] )} is sat
      boardWithOneMoreShotPlayer1 : { (all board : BoardState | boardStateWithOneMoreShot[board] and player1Turn[board] )} is unsat
    }
}

test suite for player2Turn {
    test expect {
      boardWithOneMoreShot : { (all board : BoardState | boardStateWithOneMoreShot[board] and player2Turn[board] )} is sat
      boardWithEvenNumberShotsPlayer2 : { (all board : BoardState | boardStateWithEvenNumberShots[board] and player2Turn[board] )} is unsat
    }
}

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
  }
}