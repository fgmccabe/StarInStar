worksheet{
  import topsort
  import collections

  -- test the topological sort

  assert topological([]) = []

  -- a straightforward sequence of independent entities

  def A1 is topDef{
    def orig is "one"
    def definitions is set of ["one"]
    def references is set of [] 
  }

  def A2 is topDef{
    def orig is "two"
    def definitions is set of ["two"]
    def references is set of []
  }
  def A3 is topDef{
    def orig is "three"
    def definitions is set of ["three"]
    def references is set of []
  }
  def A4 is topDef{
    def orig is "four"
    def definitions is set of ["four"]
    def references is set of []
  }

  def SA is topological(list of [A1,A2,A3,A4])

  assert size(SA) = 4

  show SA

  -- A single group

  def B1 is topDef{
    def orig is "1"
    def definitions is set of ["1"]
    def references is set of ["2"] 
  }

  def B2 is topDef{
    def orig is "2"
    def definitions is set of ["2"]
    def references is set of ["4"]
  }
  def B3 is topDef{
    def orig is "3"
    def definitions is set of ["3"]
    def references is set of ["1"]
  }
  def B4 is topDef{
    def orig is "4"
    def definitions is set of ["4"]
    def references is set of ["3"]
  }

  def SB is topological(list of [B1,B2,B3,B4])

  assert size(SB) = 1

  show SB

  -- A single group with a tail

  def C1 is topDef{
    def orig is "alpha"
    def definitions is set of ["alpha"]
    def references is set of ["beta"] 
  }

  def C2 is topDef{
    def orig is "beta"
    def definitions is set of ["beta"]
    def references is set of ["gamma"]
  }
  def C3 is topDef{
    def orig is "gamma"
    def definitions is set of ["gamma"]
    def references is set of ["alpha"]
  }
  def C4 is topDef{
    def orig is "delta"
    def definitions is set of ["delta"]
    def references is set of ["gamma"]
  }

  def CS is topological(list of [C1,C2,C3,C4])

  assert size(CS) = 2

  show CS
}