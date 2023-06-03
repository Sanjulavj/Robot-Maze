/* Robot
 * Author: Sanjula Jayawardana
 * Creation date: 2022-12-18
 */
MACHINE
    Robot

SEES
    Maze

SETS 
    CHECK_OUTPUT = {Maze_Boundary_Wall_Detected_CannotMove, Maze_Internal_Wall_Detected_CannotMove, Northward_Movement_Successful, Southward_Movement_Successful, Eastward_Movement_Successful , 
    Westward_Movement_Successful,Teleportation_Successful,Robot_Notinitialized_toEntrySquare_CannotTeleport, Robot_Cannot_Teleport_ToSameSquare,
    Maze_Boundary_Wall_Detected_CannotTeleport, Maze_Internal_Wall_Detected_CannotTeleport };
    VISITED_OUTPUT = {Yes, No, Inputs_Exceeding_Maze_Boundary_Wall};
    DIRECTION_OUPUT = { North, South, West, East, Teleported } 

DEFINITIONS
    //checking the coordinates are included in the maze area 
    checkMazePosition(xcoordinate,ycoordinate) == (xcoordinate |-> ycoordinate : AreaOfMaze);
    //checking that the robot has not reached the exit square
    checkMazeLastPosition ==  (xPosition |-> yPosition /= RobotEnds)

VARIABLES
    xPosition,
    yPosition,
    currentPosition,
    visitedSquares,
    robotPaths
    
INVARIANT
    // robot's x position belongs to the width range of the maze
    xPosition : Xcoordinate &
    // robot's y position belongs to the height range of the maze
    yPosition : Ycoordinate &
    //robot's position belongs to the maze area
    xPosition |-> yPosition : AreaOfMaze &
    //robot's current position belongs to the maze area
    currentPosition : AreaOfMaze &
    //visiting squares store as a sequence of maze items 
    visitedSquares : seq(AreaOfMaze) &
    //visiting directions store as a sequence of directions  
    robotPaths : seq(DIRECTION_OUPUT)
    
INITIALISATION
    //initializing robot's x position as the x-entry square coordinate
    xPosition := prj1(Xcoordinate, Ycoordinate)(RobotStarts) ||
    //initializing robot's y position as the y-entry square coordinate
    yPosition := prj2(Xcoordinate, Ycoordinate)(RobotStarts) ||
    //initializing current position as the entry square
    currentPosition := (RobotStarts) ||
    //initializing first visiting position as the entry square
    visitedSquares := [RobotStarts] ||
    //initializing visiting directions as an empty sequnce
    robotPaths := []



OPERATIONS
    //increases the current y-position value by one to move the robot one square north.
    output <-- MoveNorth =
        PRE 
            //checks whether the robot has not reached to the final destination and checks robot is within the maze area 
            checkMazeLastPosition & checkMazePosition(xPosition, yPosition) & output : CHECK_OUTPUT
        THEN
            // checks whether the robot moving position is within the maze area 
            IF not(checkMazePosition(xPosition, yPosition + 1))
            THEN 
                output := Maze_Boundary_Wall_Detected_CannotMove
            // checks whether the robot moving position is an internal wall
            ELSIF ((xPosition |-> yPosition + 1) : MazeWalls) 
            THEN 
                output := Maze_Internal_Wall_Detected_CannotMove
            ELSE 
                visitedSquares := (visitedSquares <- (xPosition |-> yPosition + 1)) ||
                currentPosition := (xPosition |-> yPosition + 1) ||
                yPosition := yPosition + 1 ||
                robotPaths := robotPaths <- North ||
                output := Northward_Movement_Successful
            END
        END;

    //decreases the current y-position value by one to move the robot one square south.
    output <-- MoveSouth  = 
            PRE 
                //checks whether the robot has not reached to the final destination and checks robot is within the maze area
                checkMazeLastPosition & checkMazePosition(xPosition, yPosition) & output : CHECK_OUTPUT
            THEN
                // checks whether the robot moving position is within the maze area 
                IF not(checkMazePosition(xPosition, yPosition - 1))
                THEN 
                    output := Maze_Boundary_Wall_Detected_CannotMove
                //checks whether the robot moving position is an internal wall
                ELSIF ((xPosition |-> yPosition - 1) : MazeWalls) 
                THEN 
                    output := Maze_Internal_Wall_Detected_CannotMove
                ELSE 
                    visitedSquares := (visitedSquares <- (xPosition |-> yPosition - 1)) ||
                    currentPosition := (xPosition |-> yPosition - 1) ||
                    yPosition := yPosition - 1 ||
                    robotPaths := robotPaths <- South ||
                    output := Southward_Movement_Successful
                END
            END;

    //increases the current x-position value by one to move the robot one square east.
    output <-- MoveEast =
        PRE 
            //checks whether the robot has not reached to the final destination and checks robot is within the maze area
            checkMazeLastPosition & checkMazePosition(xPosition, yPosition) & output : CHECK_OUTPUT
        THEN
             // checks whether the robot moving position is within the maze area 
            IF not(checkMazePosition(xPosition + 1, yPosition))
            THEN 
                output := Maze_Boundary_Wall_Detected_CannotMove
             //checks whether the robot moving position is an internal wall
            ELSIF ((xPosition + 1 |-> yPosition ) : MazeWalls) 
            THEN 
                output := Maze_Internal_Wall_Detected_CannotMove
            ELSE 
                visitedSquares := (visitedSquares <- (xPosition + 1 |-> yPosition)) ||
                currentPosition := (xPosition + 1 |-> yPosition ) ||
                xPosition := xPosition + 1 ||
                robotPaths := robotPaths <- East ||
                output := Eastward_Movement_Successful
            END
        END;


    //decreases the current x-position value by one to move the robot one square west.
    output <-- MoveWest =
        PRE 
            //checks whether the robot has not reached to the final destination and checks robot is within the maze area
            checkMazeLastPosition & checkMazePosition(xPosition, yPosition) & output : CHECK_OUTPUT
        THEN
             // checks whether the robot moving position is within the maze area 
            IF not(checkMazePosition(xPosition - 1, yPosition))
            THEN 
                output := Maze_Boundary_Wall_Detected_CannotMove
             //checks whether the robot moving position is an internal wall
            ELSIF ((xPosition - 1 |-> yPosition ) : MazeWalls) 
            THEN 
                output := Maze_Internal_Wall_Detected_CannotMove
            ELSE 
                visitedSquares := (visitedSquares <- (xPosition - 1 |-> yPosition)) ||
                currentPosition := (xPosition - 1 |-> yPosition ) ||
                xPosition := xPosition - 1 ||
                robotPaths := robotPaths <- West ||
                output := Westward_Movement_Successful
            END
        END;

    //teleports the robot from one square to another
    teleportOutput <-- Teleport(teleportXPosition, teleportYPosition) =
            PRE 
            //checks whether the robot has not reached to the final destination 
            checkMazeLastPosition &
            //checks robot is within the maze area
            checkMazePosition(xPosition, yPosition) &
            teleportOutput : CHECK_OUTPUT & 
            teleportXPosition : Xcoordinate & 
            teleportYPosition : Ycoordinate 
            THEN
                // checks whether the robot teleporting position is within the maze area 
                IF not(checkMazePosition(teleportXPosition, teleportYPosition))
                THEN 
                    teleportOutput := Maze_Boundary_Wall_Detected_CannotTeleport 
                // checks whether the robot initialized to the entry square
                ELSIF (size(visitedSquares) < 1) 
                THEN 
                    teleportOutput := Robot_Notinitialized_toEntrySquare_CannotTeleport 
                // checks whether the robot teleporting to the same position  
                ELSIF (teleportXPosition = xPosition & teleportYPosition = yPosition)
                THEN
                    teleportOutput := Robot_Cannot_Teleport_ToSameSquare
                //checks whether the robot teleporting position is an internal wall
                ELSIF ((teleportXPosition|-> teleportYPosition ) : MazeWalls) 
                THEN 
                    teleportOutput := Maze_Internal_Wall_Detected_CannotTeleport 
                ELSE
                    visitedSquares := (visitedSquares <- (teleportXPosition |-> teleportYPosition)) ||
                    currentPosition := (teleportXPosition |-> teleportYPosition) ||
                    robotPaths := robotPaths <- Teleported ||
                    xPosition := teleportXPosition ||
                    yPosition := teleportYPosition ||
                    teleportOutput := Teleportation_Successful
                END
                
            END;


    //ouputs the robot's current position 
    position <-- getPosition =
        BEGIN 
            position := currentPosition
        END;

    //informing whether the robot has reached to the exit square or not
    outputExitMaze <-- foundExit =
        PRE
            outputExitMaze : VISITED_OUTPUT
        THEN
            IF
                //checks whether the robot has reached to the final destination 
                not(checkMazeLastPosition)
            THEN
                outputExitMaze := Yes
            ELSE
                outputExitMaze := No
            END
        END;

    //informing if that square has been previously visited by the robot
    visitedOutput <-- visitedSquare(visitedXPosition, visitedYPosition) =
            PRE 
            visitedOutput : VISITED_OUTPUT &
            visitedXPosition : NATURAL1 & visitedYPosition : NATURAL1 & 
            visitedXPosition : Xcoordinate & visitedYPosition : Ycoordinate &
            //checks whether the robot has not reached to the final destination 
            checkMazePosition(xPosition, yPosition) 
            THEN

                IF (checkMazePosition(visitedXPosition, visitedYPosition))
                THEN 
                    //checks whether if the robot has been previously visited the relevant sqauare
                    //Moving through sequence of visited elements by removing the last element 
                    IF ((visitedXPosition |-> visitedYPosition) : ran(front(visitedSquares)))
                    THEN 
                        visitedOutput := Yes
                    ELSE
                        visitedOutput := No
                    END
                ELSE
                    visitedOutput := Inputs_Exceeding_Maze_Boundary_Wall
                END
            END;


    // outputs the pathe of the Robot
    routeOutput <-- robotsPath =
        BEGIN
            routeOutput := robotPaths
        END;
    
    // outputs the sequence of squares the Robot has visited
    visitedSquaresOutput <-- robotsRoute =
        BEGIN
            visitedSquaresOutput := visitedSquares
        END;

    //reinitialises the system
    resetMazeRobot =
        PRE
            checkMazePosition(xPosition, yPosition)
        THEN
            //reinitialises all the variables
            xPosition := prj1(Xcoordinate, Ycoordinate)(RobotStarts) ||
            yPosition := prj2(Xcoordinate, Ycoordinate)(RobotStarts) ||
            currentPosition := RobotStarts ||
            visitedSquares := [RobotStarts] ||
            robotPaths := []
    END

END
