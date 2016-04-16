worksheet{
  import testUtils

  def pT is valof parseType(parseString("(integer,integer)=>integer"),stdDict)

  def D is valof{
    var Dx := declareVar(stdDict,"__integer_plus",varEntry{loc=missing;tipe=pT})
    Dx := declareVar(Dx,"__integer_minus",varEntry{loc=missing;tipe=pT})
    Dx := declareVar(Dx,"__integer_times",varEntry{loc=missing;tipe=pT})
    valis Dx
  }
  
  def Tp is checkFile("file:arithTest.star",D)

  show Tp
}