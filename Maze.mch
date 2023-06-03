/* Maze
 * Author: Sanjula Jayawardana
 * Creation date: 2022-12-18
 */
MACHINE
    Maze

CONSTANTS
    Xcoordinate, Ycoordinate, AreaOfMaze, MazeWalls, RobotStarts, RobotEnds

PROPERTIES
    //width of the maze is restricted to 7 squares
    Xcoordinate <: NATURAL1 & Xcoordinate = 1..7 & 
    //height of the maze is restricted to 5 squares  
    Ycoordinate <: NATURAL1 & Ycoordinate = 1..5 &
    //maze area is defined as a relation between Xcoordinate and Ycoordinate range
    AreaOfMaze : Xcoordinate <-> Ycoordinate &
    //maze area presents the cartesian product of the Xcoordinate and Ycoordinate range
    AreaOfMaze = Xcoordinate * Ycoordinate &
    //internal walls are included in the maze area and it is a relation Xcoordinate and Ycoordinate range
    MazeWalls <: AreaOfMaze & MazeWalls : Xcoordinate <-> Ycoordinate &
    MazeWalls =  ({ (2 |-> 1), (6 |-> 1), (4 |-> 2), (6 |-> 2), (1 |-> 3), (2 |-> 3), (3 |-> 3), (4 |-> 3), (4 |-> 4), (6 |-> 4), (7 |-> 4), (2 |-> 5)}) &
    //entry square is included in the maze area
    RobotStarts : AreaOfMaze &
    RobotStarts = (1 |-> 1) &
    //exit square is included in the maze area
    RobotEnds : AreaOfMaze &
    RobotEnds = (1 |-> 5) 
END
