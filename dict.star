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
  } or conEntry{
    tipe has type iType
  } or contractImplementation {
    implType has type iType
  }

  type contractEntry is contractEntry{
    tipe has type iType
    spec has type iType
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

  fun declareContract(Dict,Nm,Tp,Spec) is valof {
    var D := Dict substitute { contracts = Dict.contracts[with Nm->contractEntry{tipe=Tp;spec=Spec}]}
    if Spec matches iFace(Fields,Types) then {
      for K->T in Fields do 
        D := defineVar(D,K,T)
    }
    valis D
  }

  defineVar has type (dict,string,iType) => dict
  fun defineVar(Dict,Nm,Tp) is Dict substitute {names = Dict.names[with Nm->varEntry{tipe=Tp}]}

  defineConstructor has type (dict,string,iType) => dict
  fun defineConstructor(Dict,Nm,Tp) is Dict substitute {names = Dict.names[with Nm->conEntry{tipe=Tp}]}

  introduceType has type (dict,string,iType)=>dict
  fun introduceType(Dict,Nm,Tp) is declareType(Dict,Nm,typeIs(Tp))

  fun typeOfField(Dict,algebraic(_,Cons),Nm) is valof{
    for C in Cons and findVar(Dict,C) has value conEntry{tipe=Con} do {
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
      D := declareVar(D,Ky,conEntry{tipe=ConTp})
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

  fun generalizeType(Tp,D) is generalize(Tp,(T)=>occCheck(T,D))

  private fun occCheck(iTvar{id=i;name=name;constraints=c},D) is let{
      fun check(dict{types=Tps}) where  typeIs(Tp) in Tps and occursIn(i,Tp) is some(true)
       |  check(dict{names=Vrs}) where varEntry{tipe=Tp} in Vrs and occursIn(i,Tp) is some(true)
       |  check(_) default is none
  } in (findInDict(D,check) has value X ? X : false)

  fun intersectDict(D1,D2) is D1 -- temporary definition
}