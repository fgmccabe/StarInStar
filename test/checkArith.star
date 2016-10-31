worksheet{
  import testUtils

  def pT is valof parseType(parseString("(integer,integer)=>integer"),stdDict)

  def D is valof{
    var Dx := defineVar(stdDict,"__integer_plus",cVar{loc=missing;name="__integer_plus";tipe=pT})
    Dx := defineVar(Dx,"__integer_minus",cVar{loc=missing;name="__integer_minus";tipe=pT})
    Dx := defineVar(Dx,"__integer_times",cVar{loc=missing;name="__integer_times";tipe=pT})
    valis Dx
  }
  
  def Tp is checkFile("file:arithTest.star",D)

  show Tp
}