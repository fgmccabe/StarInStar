parseType is package{
  private import errors;
  private import ast;
  private import dict;
  private import types;
  private import location;
  private import freshen;
  private import subsume;
  private import good;

  parseType(Ast,Dict) is let {
    parseTp(asName(_,Nm),BndVars) where BndVars[Nm] has value Tp is Tp;
    parseTp(asName(_,Nm),BndVars) where findType(Dict,Nm) has value Desc is
      case Desc in {
        typeIs(Tpe) is freshenForUse(Tpe)
        algebraic(Tpe,_) is freshenForUse(Tpe)
        typeAlias(_) is iType(Nm)
      }
    parseTp(asTuple(_,"()",L),BndVars) is iTuple(list of {all parseTp(E,BndVars) where E in L});

    parseTp(asTuple(_,"{}",Els),BndVars) is valof{
      var fields := dictionary of {};
      var types := dictionary of {};
      var exVars := list of [];

      for St in Els do{
        if isBinary(St,"has type") has value ((L,R)) then {
          if deParen(L) matches asName(Lc,Id) then{
            fields[Id] := parseTp(R,BndVars)
          }
          else
            reportError("Field $L should be an identifier",list of [locOf(L)]);
        } else if isBinary(St,"has kind") matches some((L,R)) then{
          if deParen(L) matches asName(_,Id) then {
            var eType is iBvar(Id);
            exVars := list of [hasKind(eType,parseKind(R)),..exVars];
            types[Id] := eType;
          }
          else
            reportError("Field $L should be an identifier",list of [locOf(L)]);
        } else if isUnary(St,"type") matches some(R) and isBinary(R,"=") matches some((Lhs,Rhs)) then{
          if deParen(Lhs) matches asName(_,Id) then {
            types[Id] := parseTp(Rhs,BndVars)
          }
          else
            reportError("Field $Lhs should be an identifier",list of [locOf(Lhs)]);
        }
        else
          reportError("Invalid element $St in record type",list of [locOf(St)]);
      }
      var reslt := iFace(fields,types);
      for HK in exVars do 
        reslt := iConstrained(reslt,HK)
      
      for hasKind(iBvar(tv),_) in exVars and not present BndVars[tv] do 
        reslt := iExists(tv,reslt);
    
      valis reslt;
    }
    parseTp(T,BndVars) where isBinary(T,"of") matches some((L,R)) is valof{
      var At is parseTp(R,BndVars);
      var Ft is parseTp(L,BndVars);
      valis checkTypeExp(Ft,At,BndVars,locOf(T))
    }
    parseTp(T,BndVars) where isBinary(T,"=>") matches some((L,R)) is valof{
      var At is parseTp(L,BndVars);
      var Ft is parseTp(R,BndVars);
      valis iFnTp(At,Ft);
    }
    parseTp(T,BndVars) where isBinary(T,"<=") matches some((L,R)) is valof{
      var At is parseTp(L,BndVars);
      var Ft is parseTp(R,BndVars);
      valis iPtTp(At,Ft);
    }
    parseTp(T,BndVars) where isBinary(T,"<=>") matches some((L,R)) is valof{
      var At is parseTp(L,BndVars);
      var Ft is parseTp(R,BndVars);
      valis iConTp(At,Ft);
    }
    parseTp(T,BndVars) where isUnary(T,"ref") matches some(R) is valof{
      var Rt is parseTp(deParen(R),BndVars);
      valis iRfTp(Rt);
    }
    parseTp(T,BndVars) where isUniv(T) has value (bVs,R) is valof{
      var M1 is leftFold(fn(m,v) => m[with v ->iBvar(v)],BndVars,bVs);
      var Bt is parseTp(R,M1)
      valis leftFold(fn(t,v)=>iUniv(v,t),Bt,bVs)
    }
    parseTp(T,BndVars) where isExists(T) matches some((bVs,R)) is valof{
      var M1 is leftFold(fn(m,v) => m[with v->iBvar(v)],BndVars,bVs);
      var Bt is parseTp(R,M1)
      valis leftFold(fn(t,v)=>iExists(v,t),Bt,bVs)
    }
    parseTp(T,BndVars) where isBinary(T,"where") matches some((L,R)) is
      parseConstraints(R,parseTp(L,BndVars),BndVars);
    parseTp(T,BndVars) default is valof{
      reportError("cannot understand type expression $(T)",list of [locOf(T)]);
      valis unTyped;
    }

    checkTypeExp(iTpExp(F,A),B,BndVars,Lc) is case subsume(Dict)(A,B) in {
      good(_) is iTpExp(F,A)
      noGood(E) is valof{
        reportError("$(iTpExp(F,A)) is not applicable to $B\nbecause $E",list of [Lc])
        valis iTpExp(F,A)
      }
    }

    parseConstraints(Cs,T,BndVars) where isBinary(Cs,"and") matches some((L,R)) is
      parseConstraints(L,parseConstraints(R,T,BndVars),BndVars);
    parseConstraints(C,T,BndVars) where isBinary(C,"over") matches some((L,R)) and
        isBinary(R,"determines") matches some((A,D)) and
        isName(L) matches some(Ct) is valof{
      var At is parseTpArgs(A,BndVars);
      var Dt is parseTpArgs(D,BndVars);
      valis iConstrained(T,iContract(Ct,At,Dt));
    }
    parseConstraints(C,T,BndVars) where isBinary(C,"over") matches some((L,R)) and
        isName(L) matches some(Ct) is valof{
      var At is parseTpArgs(L,BndVars);
      var Dt is parseTpArgs(R,BndVars);
      valis iConstrained(T,iContract(Ct,At,list of {}));
    }
    parseConstraints(C,T,BndVars) where isBinary(C,"instance of") matches some((L,R)) is
      iConstrained(T,instanceOf(parseTp(L,BndVars),parseTp(R,BndVars)));
    parseConstraints(C,T,BndVars) where isBinary(C,"implements") matches some((L,R)) and
        R matches asTuple(_,"{}",Ls) is valof{
      var t is parseTp(L,BndVars);
      var ts := T;
      for El in Ls do{
        if isBinary(El,"has type") matches some((asName(_,F),FT)) then
          ts := iConstrained(ts,iFieldCon(t,F,parseTp(FT,BndVars)))
        else if isBinary(El,"has kind") matches some((asName(_,F),FK)) then
          ts := iConstrained(ts,iFieldKind(t,F,parseKind(FK)))
      };
      valis ts;
    }
    parseConstraints(C,T,BndVars) where isBinary(C,"has kind") matches some((L,R)) is
      iConstrained(T,hasKind(parseTp(L,BndVars),parseKind(R)));

    parseTpArgs(asTuple(_,"()",L),BndVars) is
      list of {all parseTp(E,BndVars) where E in L};
    parseTpArgs(T,BndVars) is list of [parseTp(T,BndVars)];

    parseKind(asName(_,"type")) is kType;
    parseKind(K) where isBinary(K,"of") matches some((asName(_,"type"),R)) is
      kTypeFun(countTypes(R));
    parseKind(asName(_,"unknown")) is kUnknown;
    parseKind(A) is valof{
      reportError("Invalid kind specification $A",list of [locOf(A)]);
      valis kUnknown;
    }

    countTypes(asName(_,"type")) is 1;
    countTypes(asTuple(_,"()",L)) is size(L);

  } in parseTp(Ast,dictionary of [])

-- Use this when ast is properly implemented
--  isUniv(<|for all ?V such that ?T |>) is some((V,T));
  private 
  isUniv(T) where isBinary(T,"such that") matches some((L,R)) and
      isUnary(L,"for all") matches some(V) is
    some((deComma(V),R));
  isUniv(_) default is none;

  private
  isExists(T) where isBinary(T,"such that") matches some((L,R)) and
  isUnary(L,"exists") matches some(V) is
    some((deComma(V),R));
  isExists(_) default is none;

  deComma(T) where isBinary(T,",") matches some((L,R)) is
    deComma(L)++deComma(R)
  deComma(asName(_,Id)) is list of [Id]

}