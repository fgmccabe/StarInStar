parseType is package{
  private import errors;
  private import ast;
  private import dict;
  private import types;
  private import location;

  parseType(asName(_,Nm),M) where M[Nm] matches Tp is Tp;
  parseType(asTuple(_,"()",L),M) is 
    iTuple(list of {all parseType(E,M) where E in L});
  parseType(asTuple(_,"{}",Els),M) is valof{
    var fields := dictionary of {};
    var types := dictionary of {};
    var exVars := list of [];

    for St in Els do{
      if isBinary(St,"has type") matches some((L,R)) then {
        if deParen(L) matches asName(Lc,Id) then{
          fields[Id] := parseType(R,M)
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
          types[Id] := parseType(Rhs,M)
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
    
    for hasKind(iBvar(tv),_) in exVars and not present M[tv] do 
      reslt := iExists(tv,reslt);
    
    valis reslt;
  }
  parseType(T,M) where isBinary(T,"of") matches some((L,R)) is valof{
    var At is parseTypeArgs(R,M);
    var Ft is parseType(L,M);
    valis iTpExp(Ft,iTuple(At));
  }
  parseType(T,M) where isBinary(T,"=>") matches some((L,R)) is valof{
    var At is parseType(L,M);
    var Ft is parseType(R,M);
    valis iFnTp(At,Ft);
  }
  parseType(T,M) where isBinary(T,"<=") matches some((L,R)) is valof{
    var At is parseType(L,M);
    var Ft is parseType(R,M);
    valis iPtTp(At,Ft);
  }
  parseType(T,M) where isBinary(T,"<=>") matches some((L,R)) is valof{
    var At is parseType(L,M);
    var Ft is parseType(R,M);
    valis iConTp(At,Ft);
  }
  parseType(T,M) where isUnary(T,"ref") matches some(R) is valof{
    var Rt is parseType(deParen(R),M);
    valis iRfTp(Rt);
  }
  parseType(T,M) where isUniv(T) matches some((bVs,R)) is valof{
    var M1 is leftFold(fn(m,v) => m[with v ->iBvar(v)],M,bVs);
    var Bt is parseType(R,M1)
    valis leftFold(fn(t,v)=>iUniv(v,t),Bt,bVs)
  }
  parseType(T,M) where isExists(T) matches some((bVs,R)) is valof{
    var M1 is leftFold(fn(m,v) => m[with v->iBvar(v)],M,bVs);
    var Bt is parseType(R,M1)
    valis leftFold(fn(t,v)=>iExists(v,t),Bt,bVs)
  }
  parseType(T,M) where isBinary(T,"where") matches some((L,R)) is
    parseConstraints(R,parseType(L,M),M);

  parseConstraints(Cs,T,M) where isBinary(Cs,"and") matches some((L,R)) is
    parseConstraints(L,parseConstraints(R,T,M),M);
  parseConstraints(C,T,M) where isBinary(C,"over") matches some((L,R)) and
      isBinary(R,"determines") matches some((A,D)) and
      isName(L) matches some(Ct) is valof{
    var At is parseTypeArgs(A,M);
    var Dt is parseTypeArgs(D,M);
    valis iConstrained(T,iContract(Ct,At,Dt));
  }
  parseConstraints(C,T,M) where isBinary(C,"over") matches some((L,R)) and
      isName(L) matches some(Ct) is valof{
    var At is parseTypeArgs(L,M);
    var Dt is parseTypeArgs(R,M);
    valis iConstrained(T,iContract(Ct,At,list of {}));
  }

  parseConstraints(C,T,M) where isBinary(C,"instance of") matches some((L,R)) is
    iConstrained(T,instanceOf(parseType(L,M),parseType(R,M)));
  parseConstraints(C,T,M) where isBinary(C,"implements") matches some((L,R)) and
      R matches asTuple(_,"{}",Ls) is valof{
    var t is parseType(L,M);
    var ts := T;
    for El in Ls do{
      if isBinary(El,"has type") matches some((asName(_,F),FT)) then
      	ts := iConstrained(ts,iFieldCon(t,F,parseType(FT,M)))
      else if isBinary(El,"has kind") matches some((asName(_,F),FK)) then
      	ts := iConstrained(ts,iFieldKind(t,F,parseKind(FK)))
    };
    valis ts;
  }
  parseConstraints(C,T,M) where isBinary(C,"has kind") matches some((L,R)) is
    iConstrained(T,hasKind(parseType(L,M),parseKind(R)));

  parseTypeArgs(asTuple(_,"()",L),M) is
    list of {all parseType(E,M) where E in L};
  parseTypeArgs(T,M) is list of [parseType(T,M)];

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