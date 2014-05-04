sudoku is package{
  -- refactored from the Go! version

  type finiteConstraint of t is alias of list of t;

  type boardConstraint of t is alias of list of finiteConstraint of t;

  
      