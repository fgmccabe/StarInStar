stdTypes is package{
  private import canonical
  private import types
  private import parseType
  private import astUtils
  private import good
  private import location

  def stdDict is valof {
    var D := dict{
      names = dictionary of []
      types = dictionary of [
        "integer" -> typeIs{loc=missing;tipe=iType("integer")},
        "long" -> typeIs{loc=missing;tipe=iType("long")},
        "float" -> typeIs{loc=missing;tipe=iType("float")},
        "decimal" -> typeIs{loc=missing;tipe=iType("decimal")},
        "char" -> typeIs{loc=missing;tipe=iType("char")},
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
  fun stdContract(S,D) is valof introduceContract(parseString(S),D)

  private
  fun stdFun(Nm,S,D) is valof {
    def Tp is valof parseType(parseString(S),D)
    valis defineVar(D,missing,Nm,Tp)
  }
}