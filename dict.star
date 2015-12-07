dict is package{
  -- the dictionary contains descriptions of variables, types etc.
  private import canonical
  private import freshen
  private import types

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

  defineVar has type (dict,string,iType) => dict
  fun defineVar(Dict,Nm,Tp) is Dict substitute {names = Dict.names[with Nm->varEntry{tipe=Tp}]}

  fun typeOfField(Dict,algebraic(_,Cons),Nm) is valof{
    for C in Cons and findVar(Dict,C) has value varEntry{tipe=Con} do {
      if preCheck(Con,Nm) and findFieldInCon(freshen(Con),Nm) has value Tp then {
        valis some(Tp)
      }
    }
    valis none
  }

  declareAlgebraic has type (dict,string,iType,dictionary of (string,iType))=>dict
  fun declareAlgebraic(Dict,Nm,Tp,Cons) is valof{
    var D := declareType(Dict,Nm,algebraic(Tp,list of { all Ky where  Ky->_ in Cons}))
    for Ky->ConTp in Cons do
      D := declareVar(D,Ky,varEntry{tipe=ConTp})
    valis D
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

  fun generalizeType(Tp,D) is valof{
    def R is generalize(Tp,(T)=>occCheck(T,D))
    logMsg(info,"generalized $Tp in $D is $R")
    valis R
  }

  private fun occCheck(iTvar{id=i;name=name;constraints=c},D) is let{
      fun check(dict{types=Tps}) where  typeIs(Tp) in Tps and occursIn(i,Tp) is some(true)
       |  check(dict{names=Vrs}) where varEntry{tipe=Tp} in Vrs and occursIn(i,Tp) is some(true)
       |  check(_) default is none
  } in (findInDict(D,check) has value X ? X : false)

  fun intersectDict(D1,D2) is D1 -- temporary definition

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