stdTypes is package{
  private import dict
  private import types
  private import parseType
  private import astUtils
  private import good

  def stdDict is valof {
    var D := dict{
      names = dictionary of []
      types = dictionary of [
        "integer" -> typeIs(iType("integer")),
        "long" -> typeIs(iType("long")),
        "float" -> typeIs(iType("float")),
        "decimal" -> typeIs(iType("decimal")),
        "char" -> typeIs(iType("char")),
        "string" -> typeIs(iType("string"))
      ]
      contracts = dictionary of []
      outer = none
    }

    D := stdType("type boolean is true or false",D)
    D := stdType("type option of t is none or some(t)",D)

    D := stdFun("=","(integer,integer)=>boolean",D)

  --  D := stdContract("contract equality over t is { (=) has type (t,t)=>boolean; (!=) has type (t,t)=>boolean }",D)

    logMsg(info,"stddict is $D")

    valis D
  }

  private
  fun stdType(S,D) is valof parseAlgebraicType(parseString(S),D)

  private
  fun stdContract(S,D) is valof{
    def (Nm,Tp,Spec) is valof parseContract(parseString(S),D)
    valis declareContract(D,Nm,Tp,Spec)
  }

  private
  fun stdFun(Nm,S,D) is valof {
    def Tp is valof parseType(parseString(S),D)
    valis defineVar(D,Nm,Tp)
  }
}