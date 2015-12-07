contracts is package{
  private import dict
  private import canonical
  private import types

  fun implementationName(iContract{name=N; argTypes = A}) is let {
    fun allNames(list of [],soFar) is some(soFar)
     |  allNames(list of [T,..R],soFar) is switch deRef(T) in {
          case iType(Nm) is allNames(R,soFar++"#"++Nm)
          case iTpExp(TC,_) where deRef(TC) matches iType(Nm) is allNames(R,soFar++"#"++Nm)
          case _ default is none
        }
  } in allNames(A,N)

}