dict is package{
  -- the dictionary contains descriptions of variables, types etc.
  private import canonical;

  type typeEntry is typeIs(iType) -- full name of type
    or algebraic(iType,dictionary of (string,iType)) -- map of names to constructors
    or typeAlias((iType)=>maybe of iType); -- the alias is actually in the form of a function

  type varEntry is varEntry{
    tipe has type iType;
  }

  type dict is dict{
    names has type dictionary of (string, varEntry)
    types has type dictionary of (string, typeEntry)
    outer has type option of dict;
  }
  
  chain(none,L,R) is L()
  chain(some(X),L,R) is R(X)

  findType(Dict,Nm) is let {
     find(dict{types=Tp;outer=O}) is chain(Tp[Nm],fn ()=> chain(O, fn()=>none, find),fn X=>some(X))
  } in find(Dict)

  findVar(Dict,Nm) is let {
     find(dict{names=N;outer=O}) is chain(N[Nm],fn ()=> chain(O, fn()=>none, find),fn X=>some(X))
  } in find(Dict)

  declareVar(Dict,Nm,Ve) is Dict substitute { names = Dict.names[with Nm->Ve]}
  declareType(Dict,Nm,Te) is Dict substitute { types = Dict.types[with Nm->Te]}
}