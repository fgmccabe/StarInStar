worksheet{
  import parseForTest
  import parseType
  import freshen
  import check
  import canonical
  import types
  import good
  import subsume

  -- type mutually recursive factorial

  def pT is parseType(parseString("(integer,integer)=>integer"),stdDict)
  def cT is parseType(parseString("(integer,integer)=>boolean"),stdDict)

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

  def fT is parseType(parseString("(integer)=>integer"),stdDict)

  def mf is parseString("let { fun f(0) is 1 | f(N) where N>0 is times(N,g(minus(N,1))) fun g(0) is 1 | g(N) is times(N,f(minus(N,1)))} in f")


  def i is typeOfExp(mf,typeVar(),D,D)

  show i
  assert more(i,(x)=>verifyType(x,fT)) = good(true)


  fun verifyType(X,tp) is
    switch subsume(D)(X.tipe,tp) in {
      case good(_) is good(true)
      case noGood(_,_) is good(false)
    }
}