over is package{
  private import good
  private import canonical
  private import subsume
  private import freshen
  private import typeUtils
  private import access
  private import flatmap
  private import (trace)

  private transformExp has type (cExp,dictionary of (string,cExp),dictionary of (iType,cExp)) => cExp
  fun transformExp(X,S,Ov) is switch X in {
    case cVar{name=Nm} where S[Nm] has value T is T
    case cVar{} is X
    case cInt{} is X
    case cLong{} is X
    case cFloat{} is X
    case cDecimal{} is X
    case cString{} is X
   
    case cDeRef{loc=Lc;tipe=T;deref=D} is cDeRef{loc=Lc;tipe=T;deref=transformExp(D,S,Ov)}
    case cTuple{loc=Lc;tipe=T;elements=Els} is cTuple{loc=Lc;tipe=T;elements=map((El)=>transformExp(El,S,Ov),Els)}
    case cField{loc=Lc;tipe=T;record=R;field=F} is cField{loc=Lc;tipe=T;record=transformExp(R,S,Ov);field=F}
    case cFace{loc=Lc;tipe=T;values=Vls,types=Tps} is cFace{loc=Lc;tipe=T;values=dictionary of {all F->transformExp(El,S,Ov) where F->El in Vls};types=Tps}
    case cApply{loc=Lc;tipe=T;op=Op;arg=A} is cApply{loc=Lc;tipe=T;op=transformExp(op,S);arg=transformExp(A,S,Ov)}
    case cIsTrue{loc=Lc;tipe=T;cond=C} is cIsTrue{loc=Lc;tipe=T;cond=transformCond(C,S,Ov)}

    case cMemo{loc=Lc;tipe=T;value=E} is cMemo{loc=Lc;tipe=T;value=transformExp(E,S,Ov)}
    case cLambda{loc=Lc;tipe=T;lhs=L;rhs=R} is cLambda{loc=Lc;tipe=T;lhs=transformPtn(L,S,Ov);rhs=transformExp(R,S,Ov)}
    case cPttrn{loc=Lc;tipe=T;value=V;ptrn=P} is cPttrn{loc=Lc;tipe=T;value=transformExp(V,S,Ov);ptrn=transformPtn(P,S,Ov)}
    case cSwitch{loc=Lc;tipe=T;sel=E;cases=C} is cSwitch{loc=Lc;tipe=T;sel=transformExp(E,S,Ov);cases=
            map(((P,D,V))=>(transformPtn(P,S,Ov),D,transformExp(V,S,Ov)),C)}
    case cMethod{loc=Lc;tipe=T;con=C;name=Nm} is
            Ov[C] has value DV ? cField{loc=Lc;tipe=T;record=DV;field=Nm} : X
    case cLet{loc=Lc;tipe=T;env=E;stmts=St;bnd=B} is cLet{loc=Lc;tipe=T;env=E;stmts=map(transformStmt,St);bnd=transformExp(B,S,Ov)}
  }

  fun transformStmt(St,S,Ov) is switch St in {
    case canonDef(Lc,A,P,E)
                 or canonVar(srcLoc,accessMode,cPtn,cExp)
                 or canonAlgegraic(srcLoc,accessMode,iType,dictionary of (string,iType))
                 or canonAlias(srcLoc,accessMode,iType,iType)
                 or canonExists(srcLoc,accessMode,iType,iType)
                 or canonContract(srcLoc,accessMode,string,iType,iType,dictionary of (string,iType))
                 or canonImplementation(srcLoc,accessMode,iType,cExp)
  }
}