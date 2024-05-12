# CS1710 Final Project

## Project Objective
Battleship is a classic naval strategy game where two players attempt to sink each other's fleet of ships by guessing their locations on a hidden grid. Each player places a number of ships—differing in size and orientation—onto a secret board. The game proceeds in turns with players calling out grid coordinates, aiming to hit and ultimately sink their opponent’s ships. The first player to destroy all of their opponent’s vessels wins. 

With this project, we intend to model the game Battleship. We model a game board, the different types of ships in play (each can take up multiple consecutive cells) and their position on the board, hits and misses, sinking, and a win condition. We incorporate logic to distinguish between hits and misses and to track the state of each ship (intact or sunk). We hope our model helps us better understand the rules of the game, as well as strategies to win, and identify unintended behaviors and edge cases. We also hope to verify the integrity of the system, ensuring that it behaves in expected ways in all possible scenarios. According to the rules of the game, we will examine the outcomes for consistency. 


## Overview of Model

### Sigs and Predicates
#### Sigs
- `Boolean` (self-explanatory, T/F values)
- `Orientation` to define the orientation of ships, either vertical or horizontal. This affects calculations in the ship_wellformed predicate to ensure that ships don't go off the board.
- `Ship`, which contains the two fields "location" and "orientation." Locations consist of a set of Coordinates which represent the cells on the board where ships occupy. Using a set lets us represent the location of ships of various lengths. A Ship can only have one Orientation, which is either horizontal or vertical. 
- `Board`, which shows us information about the positions of ships and the status of shots that have been fired. We use partial functions from integers to either Booleans (for shots) or Ships (for ship placement)
- `Game`, for tracking the order of board states in a game. This begins with an initial board state, "first", then transitions through game states ("next")
- `BoardState`: Contains two player boards, representing individual game boards for each player. 

#### Predicates
- `ship_wellformed` to make sure that ships are placed legally on board. This includes their positioning (that all ships are properly on the board), and the count of the ships should be exactly 5. This is so that the game can start in a valid state, and prevents the illegal placement of ships that could lead to unplayable game states. 
init to a valid starting state where no shots have been fired; verifies initial ship configurations using ship_wellformed predicate. 
- `board_wellformed`, which continuously checks the validity of the game configuration (all shots are within defined range), and makes sure that ship positions don't change between different states of the game. 
- `player1Turn` and `player2Turn` are self explanatory, determining whose turn it is to play
- `balancedTurns` uses player1Turn and player2Turn to ensure that the game properly alternates between players. 
move updates the board based on the current player's shot, directly handling that action
trace outlines the overall flow of the game, simulating from start to finish
#### Functions
- `countShots` and `countShip`s are self explanatory
- `MAX` helps us to check boundaries, defining the maximum value for coordinates on the board. 

### Representation & Assumptions
Initially, ships were simply represented as Boolean values, indicating whether they were present on the grid, but this approach wasn't very conducive to enforcing game rules related to ship size/orientation. Properties like startRow, startCol, orientation and length were added to the original Ship sig. 

We ended up modeling a 7x7 board instead of a 10x10 board due to optimization problems. The main limit to our model is that it takes a long time to generate instances due to the large search space. 

## Refinements from Proposal
- Did your goals change at all from your proposal? Did you realize anything you planned was unrealistic, or that anything you thought was unrealistic was doable?
  - We had to model a 7x7 board instead of a 10x10 board due to optimization problems. 
  - We originally intended to model a win condition, but this would require generating at least the number of board states as there are ships on the board, which would take too much time and memory. Therefore, we plan to see whether going first would yield an advantage for that player by observing 5 board states.  
- We had originally designed the game using a series of different pfuncs. We thought that this implementation carried too many data structures. Thus, we rewrote the game using a ship set. This allowed us to keep track of the respective ships in a set across the whole game. This also allowed us to avoid storing ship location data in more than one location.
- Once we implemented an initial version of the game we realized that the solver found it easier to duplicate the ship instances from player 1 to player 2.


## Interpreting an Instance
Each instance starts at the top with a Game. Each game has a GameState. This atom contains Boards. These represent the boards for player 1 and player 2. Within this, the Board contains a set of ships and a pfunc that returns true or false for the grid for whether there has been a shot on that position. The set contains ships. Each ship contains a set of coordinates, each with a row and column associated with it. Thus, as the Game states increase the play also increases.

For the custom visualization, there are a total of 4 columns representing the shots taken and ships placed. The first two columns represent Player 1's boards. The first column to the left is for the shots taken by player 1 throughout the game. Cells where shots have been fired are colored red. The second column to the left is for the ships placed by player 1 on their own board, marked by the "S" symbol. The remaining two columns represent Player 2's boards, where the third column is for the shots taken by player 2 and the fourth visualizes where Player 2 has placed their ships. 


## Testing
- We've implemented tests to evaluate both model correctness and also the domain area of the game. 
- Model Correctness: To check the base mechanics and constraints of Battleship, there are checks for boundary conditions (badBoard_shots, badBoard_ships). The initial game state is also verified, as empty_board checks that an empty board is a valid state at initialization. Through all_true_inrange, we also check that the model can handle scenarios where all valid positions on the board are occupied (both by shots and ships). 
- Domain area: We tested ship rules, which involve ship count and placement as well as various sizes. There should be exactly 5 ships on the board (not more or less). Each ship should not take up more than 5 cells. We also test the initialization and progression of the game (for example, there shouldn't be any pre-fired shots). Turn mechanics between players are also tested. There is also a test suite for move that checks for a valid state after a player makes an action, which checks conditions like a consistent turn and whether their shot is valid. We thoroughly tested this predicate: there should be no repeated shots, players shouldn't move when it's not their turn, and we validated edge cases such as placing ships on the edges of the board. 

## List of Collaborators
Morgan Lo, Angela Yeung, John Finberg