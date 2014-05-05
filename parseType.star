parseType is package{
  private import ast;
  private import dict;
  private import types;
  private import location;
  private import astUtils;

  parseType(asName(_,Nm),M) where M[Nm] matches Tp is Tp;
  parseType(asTuple(_,"()",L),M) is 
    iTuple(list of {all parseType(E,M) where E in L});
  parseType(T,M) where isBinary(T,"of") matches some((L,R)) is valof{
    var At is parseTypeArgs(R,M);
    var Ft is parseType(L,M);
    valis iTpExp(Ft,At);
  }
  parseType(T,M) where isBinary(T,"=>") matches some((L,R)) is valof{
    var At is parseType(L,M);
    var Ft is parseType(R,M);
    valis iFnTp(At,Ft);
  }
  parseType(T,M) where isUnary(T,"ref") matches some(R) is valof{
    var Rt is parseType(deParen(R),M);
    valis iRfTp(Rt);
  }
  parseType(T,M) where isUniv(T) matches some((V,R)) is valof{
    var bVs is _map(V,fn asName(_,v)=>v);
    var M1 is leftFold(fn(m,v) => m[with v ->iBvar(v)],M,bVs);
    var Bt is parseType(R,M1)
    valis leftFold(fn(t,v)=>iUniv(v,t),Bt,bVs)
  }
  parseType(T,M) where isExists(T) matches some((V,R)) is valof{
    var bVs is _map(V,fn asName(_,v)=>v);
    var M1 is leftFold(fn(m,v) => m[with v->iBvar(v)],M,bVs);
    var Bt is parseType(R,M1)
    valis leftFold(fn(t,v)=>iExists(v,t),Bt,bVs)
  }
  parseType(T,M) where isBinary(T,"where") matches some((L,R)) is
    parseConstraints(R,parseType(L,M),M);

  parseConstraints(Cs,T,M) where isBinary(Cs,"'n") matches some((L,R)) is
    parseConstraints(L,parseConstraints(R,T,M),M);
  parseConstraints(C,T,M) where isBinary(C,"over") matches some((L,R)) is valof{
    var At is parseTypeArgs(R,M);
    var Ft is parseType(L,M);
    valis iConstrained(T,iContract(iTpExp(Ft,At)))
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
    iTuple(list of {all parseType(E,M) where E in L});
  parseTypeArgs(T,M) is iTuple(list of {parseType(T,M)});

  parseKind(asName(_,"type")) is kType;
  parseKind(K) where isBinary(K,"of") matches some((asName(_,"type"),R)) is
    kTypeFun(countTypes(R));
  parseKind(asName(_,"unknown")) is kUnknown;

  countTypes(asName(_,"type")) is 1;
  countTypes(asTuple(_,"()",L)) is size(L);

}
    
  
  

    
  
