stdTypes is package{
  private import canonical
  private import types
  private import parseType
  private import astUtils
  private import good
  private import location

  def booleanType is iType("boolean")

  def stdDict is valof {
    var D := dict{
      names = dictionary of []
      types = dictionary of [
        "integer" -> typeIs{loc=missing;tipe=iType("integer")},
        "float" -> typeIs{loc=missing;tipe=iType("float")},
        "string" -> typeIs{loc=missing;tipe=iType("string")}
      ]
      contracts = dictionary of []
      implementations = dictionary of []
      outer = none
    }

    D := stdType("type boolean is true or false",D)
    D := stdType("type option of t is none or some(t)",D)

    D := stdFun("=","for all t such that (t,t)=>boolean",D)

  --  D := stdContract("contract equality over t is { (=) has type (t,t)=>boolean; (!=) has type (t,t)=>boolean }",D)

  --  logMsg(info,"stddict is $D")

    valis D
  }

  private
  fun stdType(S,D) is valof parseAlgebraicType(parseString(S),D)

  private
  fun stdContract(S,D) is valof{
    def (Nm,entry) is valof parseContract(parseString(S),D)
    valis declareContract(D,Nm,entry)
  }

  private
  fun stdFun(Nm,S,D) is valof {
    def Tp is valof parseType(parseString(S),D)
    valis defineVar(D,Nm,cVar{loc=missing;name=Nm;tipe=Tp})
  }
}