parseType is package{
  private import errors
  private import ast
  private import dict
  private import types
  private import location
  private import freshen
  private import subsume
  private import good

  fun parseType(Ast,Dict) is let {
    fun parseTp(asName(_,Nm),BndVars) where BndVars[Nm] has value Tp is Tp
     |  parseTp(asName(_,Nm),BndVars) where findType(Dict,Nm) has value Desc is
          switch Desc in {
            case typeIs(Tpe) is freshen(Tpe)
            case algebraic(Tpe,_) is freshen(Tpe)
            case typeAlias(_) is iType(Nm)
          }
     |  parseTp(asTuple(_,"()",L),BndVars) is iTuple(list of {all parseTp(E,BndVars) where E in L})
     |  parseTp(asTuple(_,"{}",Els),BndVars) is valof{
          var fields := dictionary of []
          var types := dictionary of []
          var exVars := list of []

          for St in Els do{
            switch St in {
              case isBinary(_,"has type",L,R) do {
                if deParen(L) matches asName(Lc,Id) then{
                  fields[Id] := parseTp(R,BndVars)
                }
                else
                  reportError("Field $L should be an identifier",list of [locOf(L)])
              }
              case isBinary(_,"has kind",L,R) do {
                if deParen(L) matches asName(_,Id) then {
                  def eType is iBvar(Id)
                  exVars := list of [hasKind(eType,parseKind(R)),..exVars]
                  types[Id] := eType
                }
                else
                  reportError("Field $L should be an identifier",list of [locOf(L)])
              }
              case isUnary(_,"type",isBinary(_,"=",Lhs,Rhs)) do {
                if deParen(Lhs) matches asName(_,Id) then {
                    types[Id] := parseTp(Rhs,BndVars)
                  }
                  else
                    reportError("Field $Lhs should be an identifier",list of [locOf(Lhs)])
              }
              case _ default do 
                reportError("Invalid element $St in record type",list of [locOf(St)])
            }
          }
          var reslt := iFace(fields,types)
          for HK in exVars do 
            reslt := iConstrained(reslt,HK)
          
          for hasKind(iBvar(tv),_) in exVars and not present BndVars[tv] do 
            reslt := iExists(tv,reslt)
        
          valis reslt
        }
     |  parseTp(isBinary(_,"of",L,R),BndVars) is valof{
          def At is parseTp(R,BndVars)
          def Ft is parseTp(L,BndVars)
          valis checkTypeExp(Ft,At,BndVars,locOf(L))
        }
     |  parseTp(isBinary(_,"=>",L,R),BndVars) is valof{
          def At is parseTp(L,BndVars)
          def Ft is parseTp(R,BndVars)
          valis iFnTp(At,Ft)
        }
     |  parseTp(isBinary(_,"<=",L,R),BndVars) is valof{
          def At is parseTp(L,BndVars)
          def Ft is parseTp(R,BndVars)
          valis iPtTp(At,Ft)
        }
     |  parseTp(isBinary(_,"<=>",L,R),BndVars) is valof{
          def At is parseTp(L,BndVars)
          def Ft is parseTp(R,BndVars)
          valis iConTp(At,Ft)
        }
     |  parseTp(isUnary(_,"ref",R),BndVars) is valof{
          def Rt is parseTp(deParen(R),BndVars)
          valis iRfTp(Rt)
        }
     |  parseTp(T,BndVars) where isUniv(T) has value (bVs,R) is valof{
          def M1 is leftFold(fn(m,v) => m[with v ->iBvar(v)],BndVars,bVs)
          def Bt is parseTp(R,M1)
          valis leftFold(fn(t,v)=>iUniv(v,t),Bt,bVs)
        }
     |  parseTp(T,BndVars) where isExists(T) has value (bVs,R) is valof{
          def M1 is leftFold(fn(m,v) => m[with v->iBvar(v)],BndVars,bVs)
          def Bt is parseTp(R,M1)
          valis leftFold(fn(t,v)=>iExists(v,t),Bt,bVs)
        }
     |  parseTp(isBinary(_,"where",L,R),BndVars) is
          parseConstraints(R,parseTp(L,BndVars),BndVars)
     |  parseTp(T,BndVars) default is valof{
          reportError("cannot understand type expression $(T)",list of [locOf(T)])
          valis unTyped
        }

    fun checkTypeExp(iTpExp(F,A),B,BndVars,Lc) is switch subsume(Dict)(A,B) in {
      case good(_) is iTpExp(F,A)
      case noGood(E) is valof{
        reportError("$(iTpExp(F,A)) is not applicable to $B\nbecause $E",list of [Lc])
        valis iTpExp(F,A)
      }
    }

    fun parseConstraints(isBinary(_,"and",L,R),T,BndVars) is
          parseConstraints(L,parseConstraints(R,T,BndVars),BndVars)
     |  parseConstraints(isBinary(_,"over",L,isBinary(_,"determines",A,D)),T,BndVars) where 
        isName(L) has value Ct is valof{
          def At is parseTpArgs(A,BndVars)
          def Dt is parseTpArgs(D,BndVars)
          valis iConstrained(T,iContractCon(iContract{name=Ct;argTypes=At;depTypes=Dt}))
        }
     |  parseConstraints(isBinary(_,"over",L,R),T,BndVars) where 
        isName(L) has value Ct is valof{
          def At is parseTpArgs(L,BndVars)
          def Dt is parseTpArgs(R,BndVars)
          valis iConstrained(T,iContractCon(iContract{name=Ct;argTypes=At;depTypes=list of []}))
        }
     |  parseConstraints(isBinary(_,"instance of",L,R),T,BndVars) is
          iConstrained(T,instanceOf(parseTp(L,BndVars),parseTp(R,BndVars)))
     |  parseConstraints(isBinary(_,"implements",L,asTuple(_,"{}",Ls)),T,BndVars) is valof{
          def t is parseTp(L,BndVars)
          var ts := T
          for El in Ls do{
            if El matches isBinary(_,"has type",asName(_,F),FT) then
              ts := iConstrained(ts,iFieldCon(t,F,parseTp(FT,BndVars)))
            else if El matches isBinary(_,"has kind",asName(_,F),FK) then
              ts := iConstrained(ts,iFieldKind(t,F,parseKind(FK)))
          }
          valis ts
        }
     |  parseConstraints(isBinary(_,"has kind",L,R),T,BndVars) is
          iConstrained(T,hasKind(parseTp(L,BndVars),parseKind(R)))

    fun parseTpArgs(asTuple(_,"()",L),BndVars) is
          list of {all parseTp(E,BndVars) where E in L}
     |  parseTpArgs(T,BndVars) is list of [parseTp(T,BndVars)]

    fun parseKind(asName(_,"type")) is kType
     |  parseKind(isBinary(_,"of",asName(_,"type"),R)) is kTypeFun(countTypes(R))
     |  parseKind(asName(_,"unknown")) is kUnknown
     |  parseKind(A) is valof{
          reportError("Invalid kind specification $A",list of [locOf(A)])
          valis kUnknown
        }

    fun countTypes(asName(_,"type")) is 1
     |  countTypes(asTuple(_,"()",L)) is size(L)

  } in parseTp(Ast,dictionary of [])

-- Use this when ast is properly implemented
--  isUniv(<|for all ?V such that ?T |>) is some((V,T))
  private 
  fun isUniv(isBinary(_,"such that",isUnary(_,"for all",V),R)) is some((deComma(V),R))
   |  isUniv(_) default is none

  private
  fun isExists(isBinary(_,"such that",isUnary(_,"for all",V),R)) is some((deComma(V),R))
   |  isExists(_) default is none

  fun deComma(isBinary(_,",",L,R)) is deComma(L)++deComma(R)
   |  deComma(asName(_,Id)) is list of [Id]
}