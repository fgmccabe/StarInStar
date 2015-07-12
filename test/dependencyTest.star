worksheet{
  import dependencies
  import parseForTest
  import dict

  def F is parseString("fun f(0) is 1 | f(N) where N>0 is g(N-1)*N")
  def G is parseString("fun g(0) is 1 | g(N) where N>0 is f(N-1)*N")
  def P is list of [F,G]

  def DP is dependencies(P)

  assert size(DP) = 1

  def G1 is someValue(DP[0])

  assert size(G1) = 2

  show G1

  def CB is parseString("type cons of t is nil or cons(t,bar of t)")
  def BC is parseString("type bar of s is bar(cons of t)")

  def DC is dependencies(list of [CB,BC])

  assert size(DC) = 1
  def DC1 is someValue(DC[0])
  assert size(DC1) = 2
  show DC

  -- A test which mixes values and types

  def NN is parseString("fun now() is 34")
  def MM is parseString("type p is p{dob has type integer; dob default is now()}")

  show dependencies(list of [MM,NN])
}