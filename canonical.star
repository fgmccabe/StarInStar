canonical is package{
  private import location
  private import operators
  import types

  -- define the typed term structure. This is the main workhorse structure for representing Star programs

  -- A definition statement
  type canonStmt is canonDef(srcLoc,cPtn,cExp)
                 or canonVar(srcLoc,cPtn,cExp)
                 or canonType(srcLoc,iType,cType)

  implementation hasLocation over canonStmt is {
    fun locOf(canonDef(Lc,_,_)) is Lc
     |  locOf(canonType(Lc,_,_)) is Lc
     |  locOf(canonVar(Lc,_,_)) is Lc
  }

  implementation pPrint over canonStmt is {
    ppDisp = shw
  } using {
    fun shw(E) is ppSequence(0,[showStmt(E),ppStr("@"),ppDisp(locOf(E))])
  }

   private
  fun showCanonSeq([],_) is []
   |  showCanonSeq([P],S) is [S(P)]
   |  showCanonSeq([P,..R],S) is [S(P),ppStr(";"),ppNl,..showCanonSeq(R,S)]

  private
  fun showStmt(S) is switch(S) in {
    case canonDef(_,Vr,Vl) is ppSequence(0,[ppStr("def"),ppSpace,showPtn(Vr,1199),ppStr(":"),ppDisp(Vr.tipe),ppSpace,ppStr("is"),ppSpace,showExp(Vl,1199)])
    case canonVar(_,Vr,Vl) is ppSequence(0,[ppStr("var"),ppSpace,showPtn(Vr,1199),ppStr(":"),ppDisp(Vr.tipe),ppSpace,ppStr(":="),ppSpace,showExp(Vl,1199)])
    case canonType(_,Tp,Tdef) is ppSequence(0,[ppStr("type"),ppSpace,dispTypeDef(Tdef)])
  }

  -- Canonical expression term
  type cExp is 
       cVar{loc has type srcLoc; tipe has type iType; name has type string}   -- a variable of some form
    or cDeRef{loc has type srcLoc; tipe has type iType; deref has type cExp}  -- dereference a variable
    or cInt{loc has type srcLoc; tipe has type iType; ival has type integer}
    or cLong{loc has type srcLoc; tipe has type iType; lval has type long}
    or cFloat{loc has type srcLoc; tipe has type iType; fval has type float}
    or cDecimal{loc has type srcLoc; tipe has type iType; dval has type decimal}
    or cChar{loc has type srcLoc; tipe has type iType; cval has type char}
    or cString{loc has type srcLoc; tipe has type iType; sval has type string}
    or cTuple{loc has type srcLoc; tipe has type iType; elements has type list of cExp}
    or cFace{loc has type srcLoc; tipe has type iType; values has type dictionary of (string,cExp);types has type dictionary of (string,iType)}
    or cField{loc has type srcLoc; tipe has type iType; record has type cExp; field has type string}
    or cApply{loc has type srcLoc; tipe has type iType; op has type cExp; arg has type cExp}
    or cSwitch{loc has type srcLoc; tipe has type iType; sel has type cExp; cases has type list of ((cPtn,boolean,cExp))}
    or cLet{loc has type srcLoc;tipe has type iType;env has type list of canonStmt;bnd has type cExp}
    or cLambda{loc has type srcLoc; tipe has type iType; lhs has type cPtn; rhs has type cExp}
    or cMemo{loc has type srcLoc; tipe has type iType; value has type cExp}

  implementation pPrint over cExp is {
    ppDisp = shw
  } using {
    fun shw(E) is ppSequence(0,[showExp(E,2000),ppSpace,ppStr(":"),ppSpace,showType(E.tipe,2000),ppStr("@"),ppDisp(E.loc)])
  }

  private
  fun showExp(E,Pr) is switch E in {
    case cVar{name=Nm} is ppStr(Nm)
    case cDeRef{deref=C} is parenthesize(ppSequence(0,[ppStr("!"),showExp(C,149)]),Pr>=150)
    case cInt{ival=Ix} is ppStr(Ix as string)
    case cLong{lval=Lx} is ppStr(Lx as string)
    case cFloat{fval=Dx} is ppStr(Dx as string)
    case cDecimal{dval=Dx} is ppStr(Dx as string)
    case cChar{cval=Cx} is ppSequence(0,cons of [ ppStr("'"), ppStr(Cx as string), ppStr("'")])
    case cString{sval=Sx} is ppSequence(0,cons of [ ppStr("\""), ppStr(Sx), ppStr("\"")])
    case cTuple{elements=Tpl} is ppSequence(0,[ppStr("("),
                                      ppSequence(0,interleave(cons of { all showExp(El,999) where El in Tpl},ppStr(", "))),
                                    ppStr(")")])
    case cFace{values=Values;types=Types} is ppSequence(0,[ppStr("{"),
                                      ppSequence(0,interleave(cons of { all 
                                          ppSequence(0,[ppStr(Ky),ppStr("="),showExp(Vl,899)]) where Ky->Vl in Values},ppStr(";"))),
                                      interSemi(size(Values),size(Types)),
                                      ppSequence(0,interleave(cons of { all
                                          ppSequence(0,[ppStr("type"),ppSpace,ppStr(Ky),ppStr("="),ppSpace,showType(Tp,899)]) 
                                          where Ky->Tp in Types},ppStr(";"))),
                                      ppStr("}")])
    case cField{record=Rc;field=Fld} is parenthesize(ppSequence(0,[showExp(Rc,174),ppStr("."),ppStr(Fld)]),Pr>=175)
    case cApply{op=Op;arg=Args} is ppSequence(0,[showExp(Op,0),parenthesize(showExp(Args,0),Args matches cTuple{})])
    case cLambda{lhs=Args;rhs=Exp} is parenthesize(ppSequence(0,[showPtn(Args,909),ppSpace,ppStr("=>"),ppSpace,showExp(Exp,910)]),Pr>=910)
    case cMemo{value=Exp} is parenthesize(ppSequence(0,[ppStr("memo"),ppSpace,showExp(Exp,998)]),Pr>=999)
    case cLet{env=Env;bnd=B} is parenthesize(ppSequence(0,[ppStr("let"),ppSpace,ppStr("{"),ppNl,ppSequence(2,showCanonSeq(Env,showStmt)),ppNl,ppStr("}"),ppSpace,ppStr("in"),ppSpace,showExp(B,907)]),Pr>=908)
    case cSwitch{cases=Cs;sel=S} is parenthesize(ppSequence(0,[ppStr("switch"),ppSpace,showExp(S,907),ppSpace,ppStr("in"),ppSpace,ppStr("{"),ppNl,ppSequence(2,showCases(Cs,showExpCase)),ppNl,ppStr("}")]),Pr>=908)
    case _ default is ppStr(__display(E))
  }

  implementation hasLocation over cExp is {
    fun locOf(E) is E.loc
  }

  private
  fun showCases([],_) is []
   |  showCases([(P,D,E)],S) is [S(P,D,E)]
   |  showCases([(P,D,E),..R],S) is [S(P,D,E),ppStr(";"),ppNl,..showCases(R,S)]

  private
  fun showExpCase(P,false,E) is ppSequence(0,[ppStr("case"),ppSpace,showPtn(P,1290),ppSpace,ppStr("is"),ppSpace,showExp(E,1289)])
   |  showExpCase(P,true,E) is ppSequence(0,[ppStr("case"),ppSpace,showPtn(P,1290),ppSpace,ppStr("default"),ppSpace,ppStr("is"),ppSpace,showExp(E,1289)])

  -- Canonical pattern term
  type cPtn is 
       pVar{loc has type srcLoc; tipe has type iType; name has type string} -- a new variable
    or pInt{loc has type srcLoc; tipe has type iType; ival has type integer}
    or pLong{loc has type srcLoc; tipe has type iType; lval has type long}
    or pFloat{loc has type srcLoc; tipe has type iType; fval has type float}
    or pDecimal{loc has type srcLoc; tipe has type iType; dval has type decimal}
    or pChar{loc has type srcLoc; tipe has type iType; cval has type char}
    or pString{loc has type srcLoc; tipe has type iType; sval has type string}
    or pTuple{loc has type srcLoc; tipe has type iType; elements has type list of cPtn}
    or pFace{loc has type srcLoc; tipe has type iType; values has type dictionary of (string,cPtn); types has type dictionary of (string,iType)}
    or pWhere{loc has type srcLoc; tipe has type iType; ptrn has type cPtn;cond has type cCond}
    or pApply{loc has type srcLoc; tipe has type iType; op has type cExp;arg has type cPtn}

  implementation pPrint over cPtn is {
    ppDisp = shw
  } using {
    fun shw(E) is ppSequence(0,[showPtn(E,2000),ppSpace,ppStr(":"),ppSpace,showType(E.tipe,2000),ppStr("@"),ppDisp(E.loc)])
  }

  fun emptyPtnTuple(Lc) is pTuple{loc=Lc;tipe = iTuple([]); elements = []}

  private
  fun showPtn(P,Pr) is switch P in {
    case pVar{name=Nm} is ppStr(Nm)
    case pInt{ival=Ix} is ppStr(Ix as string)
    case pLong{lval=Lx} is ppStr(Lx as string)
    case pFloat{fval=Dx} is ppStr(Dx as string)
    case pDecimal{dval=Dx} is ppStr(Dx as string)
    case pChar{cval=Cx} is ppSequence(0,cons of [ ppStr("'"), ppStr(Cx as string), ppStr("'")])
    case pString{sval=Sx} is ppSequence(0,cons of [ ppStr("\""), ppStr(Sx), ppStr("\"")])
    case pTuple{elements=Tpl} is ppSequence(0,[ppStr("("),
                                      ppSequence(0,interleave(cons of { all showPtn(El,999) where El in Tpl},ppStr(", "))),
                                    ppStr(")")])
    case pFace{values=Values;types=Types} is ppSequence(0,[ppStr("{"),
                                      ppSequence(0,interleave(cons of { all 
                                          ppSequence(0,[ppStr(Ky),ppStr("="),showPtn(Vl,1300)]) where Ky->Vl in Values},ppStr(";"))),
                                      interSemi(size(Values),size(Types)),
                                      ppSequence(0,interleave(cons of { all
                                          ppSequence(0,[ppStr("type"),ppSpace,ppStr(Ky),ppStr("="),ppSpace,showType(Tp,899)]) 
                                          where Ky->Tp in Types},ppStr(";"))),
                                      ppStr("}")])
    case pWhere{ptrn=Ptn;cond=Guard} is parenthesize(ppSequence(0,[showPtn(Ptn,939),ppSpace,ppStr("where"),ppSpace,showCond(Guard,939)]),Pr>=940)
    case pApply{op=Op;arg=Args} is ppSequence(0,[showExp(Op,0),parenthesize(showPtn(Args,0),Args matches pTuple{})])
  }

  -- Canonical condition term
  type cCond is 
       cAnd{loc has type srcLoc; lhs has type cCond; rhs has type cCond}
    or cOr{loc has type srcLoc; lhs has type cCond; rhs has type cCond}
    or cNot{loc has type srcLoc; rhs has type cCond}
    or cImplies{loc has type srcLoc; lhs has type cCond; rhs has type cCond}
    or cOtherwise{loc has type srcLoc; lhs has type cCond; rhs has type cCond}
    or cCond{loc has type srcLoc; tst has type cCond; lhs has type cCond; rhs has type cCond}
    or cSearch{loc has type srcLoc; gen has type cPtn; src has type cExp}
    or cIxSearch{loc has type srcLoc; gen has type cPtn; key has type cPtn; src has type cExp}
    or cExp{loc has type srcLoc; exp has type cExp}


  implementation pPrint over cCond is {
    ppDisp = shw
  } using {
    fun shw(E) is ppSequence(0,[showCond(E,2000),ppStr("@"),ppDisp(E.loc)])
  }

  private
  fun showCond(C,Pr) is switch C in {
    case cAnd{lhs=L;rhs=R} is parenthesize(ppSequence(0,[showCond(L,919),ppSpace,ppStr("and"),ppSpace,showCond(R,920)]),Pr>=920)
    case cOr{lhs=L;rhs=R} is parenthesize(ppSequence(0,[showCond(L,929),ppSpace,ppStr("or"),ppSpace,showCond(R,930)]),Pr>=930)
    case cNot{rhs=R} is parenthesize(ppSequence(0,[ppStr("not"),ppSpace,showCond(R,909)]),Pr>=910)
    case cImplies{lhs=L;rhs=R} is parenthesize(ppSequence(0,[showCond(L,919),ppSpace,ppStr("implies"),ppSpace,showCond(R,920)]),Pr>=920)
    case cOtherwise{lhs=L;rhs=R} is parenthesize(ppSequence(0,[showCond(L,929),ppSpace,ppStr("otherwise"),ppSpace,showCond(R,930)]),Pr>=930)
    case cCond{tst=T;lhs=L;rhs=R} is parenthesize(ppSequence(0,[showCond(T,949),ppStr("?"),showCond(L,949),ppSpace,ppStr(":"),ppSpace,showCond(R,9590)]),Pr>=960)
    case cSearch{gen=L;src=R} is parenthesize(ppSequence(0,[showPtn(L,907),ppSpace,ppStr("in"),ppSpace,showExp(R,907)]),Pr>=908)
    case cIxSearch{key=K;gen=V;src=R} is parenthesize(ppSequence(0,[showPtn(K,899),ppSpace,ppStr("->"),showPtn(V,899),ppSpace,
              ppStr("in"),ppSpace,showExp(R,907)]),Pr>=908)
    case cExp{exp=E} is showExp(E,Pr)
  }

  -- Type definition
  type cType is 
    cAlgebraic(Lc,dictionary of (string,iType)) -- algebraic type has a set of constructors

  private
  fun dispTypeDef(cAlgebraic(_,Cons)) is ppSequence(0,[ppStr("is"),ppSpace,..interleave(cons of {all ppDisp(X) where _->X in Cons},ppStr("or"))])

  implementation pPrint over cType is {
    ppDisp = dispTypeDef
  }
  
  private
  fun interSemi(0,_) is ppSpace
   |  interSemi(_,0) is ppSpace
   |  interSemi(_,_) default is ppStr(";")

  private 
  fun parenthesize(E,true) is E
   |  parenthesize(E,false) is ppSequence(0,cons of [ppStr("("), E, ppStr(")")])
}