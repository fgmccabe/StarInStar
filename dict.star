dict is package{
  -- the dictionary contains descriptions of variables, types etc.
  private import canonical
  private import freshen

  type typeEntry is typeIs(iType) -- full name of type
    or algebraic(iType,list of string) -- collect names of constructors
    or typeAlias((iType)=>option of iType); -- the alias is actually in the form of a function

  type varEntry is varEntry{
    tipe has type iType
  } or contractImplementation {
    implType has type iContract
  }

  type contractEntry is contractEntry{
    tipe has type iContract
    spec has type iType -- actually a constructor type
  }

  type dict is dict{
    names has type dictionary of (string, varEntry)
    types has type dictionary of (string, typeEntry)
    contracts has type dictionary of (string, contractEntry)
    outer has type option of dict
  }
  
  fun chain(none,L,R) is L()
   |  chain(some(X),L,R) is R(X)

  private fun findInDict(Dict, local) is let {
    fun find(D) where local(D) has value X is some(X)
     |  find(dict{outer = O}) where O has value OD is find(OD)
     |  find(_) default is none
  } in find(Dict)

  fun findType(Dict,Nm) is findInDict(Dict, (dict{types=T}) => T[Nm])
  fun findVar(Dict,Nm) is findInDict(Dict, (dict{names=N})=>N[Nm])
  fun findContract(Dict,Nm) is findInDict(Dict, (dict{contracts=C})=>C[Nm])

  fun declareVar(Dict,Nm,Ve) is Dict substitute { names = Dict.names[with Nm->Ve]}
  fun declareType(Dict,Nm,Te) is Dict substitute { types = Dict.types[with Nm->Te]}

  fun typeOfField(Dict,algebraic(_,Cons),Nm) is valof{
    for C in Cons and findVar(Dict,C) has value varEntry{tipe=Con} do {
      if preCheck(Con,Nm) and findFieldInCon(freshenForUse(Con),Nm) has value Tp then {
        valis some(Tp)
      }
    }
    valis none
  }

  private
  fun preCheck(iUniv(_,T),Nm) is preCheck(T,Nm)
   |  preCheck(iExists(_,T),Nm) is preCheck(T,Nm)
   |  preCheck(iConstrained(T,_),Nm) is preCheck(T,Nm)
   |  preCheck(iConTp(L,R),Nm) is preCheck(L,Nm)
   |  preCheck(iFace(L,R),Nm) is present L[Nm] or present R[Nm]
   |  preCheck(_,_) default is false

  fun findFieldInCon(iConTp(L,R),Nm) is findFieldInCon(L,Nm)
   |  findFieldInCon(iFace(L,_),Nm) is L[Nm]
   |  findFieldInCon(_,_) default is none

  def stdDict is dict{
    names = dictionary of [
      "none"->varEntry{tipe = iUniv("t",iTpExp(iType("option"),iBvar("t")))},
      "some"->varEntry{tipe = iUniv("t",iConTp(iBvar("t"),iTpExp(iType("option"),iBvar("t"))))}]
    types = dictionary of [
      "integer" -> typeIs(iType("integer")),
      "long" -> typeIs(iType("long")),
      "float" -> typeIs(iType("float")),
      "decimal" -> typeIs(iType("decimal")),
      "char" -> typeIs(iType("char")),
      "string" -> typeIs(iType("string")),
      "option" -> algebraic(iUniv("t",iTpExp(iType("option"),iBvar("t"))),["none", "some"])
    ]
    contracts = dictionary of []
    outer = none
  }
}