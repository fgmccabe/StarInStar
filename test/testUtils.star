testUtils is package{
  import parseForTest
  import parseType
  import freshen
  import check
  import canonical
  import types
  import good
  import subsume
  import stdTypes

  fun checkFile(Fn,D) is good computation {
    def Ast is parseFile(Fn)
    valis valof typeOfProgram(Ast,D)
  }
}