arithTest is package{
  -- Test contract definition and implementation

  contract arith over t is {
    (+) has type (t,t)=>t
    (-) has type (t,t)=>t
    (*) has type (t,t)=>t
    _minus has type (t)=>t
  }

  implementation arith over integer is {
    (+) = __integer_plus
    (-) = __integer_minus
    (*) = __integer_times
    _minus = ((X)=>0-X)
  }

  fun fact(0) is 1
   |  fact(N) is N*fact(N-1)
}