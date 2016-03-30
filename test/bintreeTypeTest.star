worksheet{
  import parseForTest
  import parseType
  import freshen
  import dict
  import check
  import canonical
  import types
  import good
  import subsume
  import stdTypes

  def pT is valof parseType(parseString("(integer,integer)=>integer"),stdDict)
  def cT is valof parseType(parseString("(integer,integer)=>boolean"),stdDict)

  def D is valof{
    var Dx := declareVar(stdDict,"plus",varEntry{tipe=pT})
    Dx := declareVar(Dx,"minus",varEntry{tipe=pT})
    Dx := declareVar(Dx,"times",varEntry{tipe=pT})
    Dx := declareVar(Dx,">",varEntry{tipe=cT})
    Dx := declareVar(Dx,"<",varEntry{tipe=cT})
    Dx := declareVar(Dx,">=",varEntry{tipe=cT})
    Dx := declareVar(Dx,"=<",varEntry{tipe=cT})
    valis Dx
  }

  def mf is parseString("let { type tree of t is nil or n(tree of t,t,tree of t) fun find(nil,_) is false | find(n(L,Lb,R),T) where Lb=T is true | find(n(L,Lb,R),T) where Lb<T is find(R,T) | find(n(L,_,R),T) default is find(L,T)} in find")

  show mf

  show typeOfExp(mf,typeVar(),D,D)

}