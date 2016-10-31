canonical is package{
  private import location
  private import operators
  private import freshen
  private import access
  private import (trace)
  import types

  -- define the typed term structure. This is the main workhorse structure for representing Star programs

  type canonProgram is canonPackage{
    loc has type srcLoc
    name has type string
    imports has type dictionary of (string,iType)
    pkg has type cExp
    assert pkg matches cLambda{} or pkg matches cMemo{}
  }

  implementation hasLocation over canonProgram is {
    fun locOf(E) is E.loc
  }

  contract isExported over t is {
    exported has type (t)=>set of cExp
  }

  -- A definition statement
  type canonStmt is canonDef(srcLoc,accessMode,cPtn,cExp)
                 or canonVar(srcLoc,accessMode,cPtn,cExp)
                 or canonAlgegraic(srcLoc,accessMode,iType,dictionary of (string,iType))
                 or canonAlias(srcLoc,accessMode,iType,iType)
                 or canonExists(srcLoc,accessMode,iType,iType)
                 or canonContract(srcLoc,accessMode,string,iType,iType,dictionary of (string,iType))
                 or canonImplementation(srcLoc,accessMode,iType,cExp)

                 -- or canonAction(srcLoc,cAction)

  implementation hasLocation over canonStmt is {
    fun locOf(canonDef(Lc,_,_,_)) is Lc
     |  locOf(canonVar(Lc,_,_,_)) is Lc
     |  locOf(canonAlgegraic(Lc,_,_,_)) is Lc
     |  locOf(canonContract(Lc,_,_,_,_,_)) is Lc
     |  locOf(canonImplementation(Lc,_,_,_)) is Lc
  }

  implementation pPrint over canonStmt is {
    ppDisp = shw
  } using {
    fun shw(E) is ppSequence(0,[showStmt(E),ppStr("@"),ppDisp(locOf(E))])
  }

  implementation isExported over canonStmt is let {
    fun definedInStmt(canonDef(_,pUblic,P,_)) is exported(P)
     |  definedInStmt(canonVar(_,pUblic,P,_)) is exported(P)
     |  definedInStmt(canonImplementation(Lc,pUblic,Tp,_)) where implName(Tp) has value INm is 
          set of [cVar{loc=Lc;tipe=Tp;name=INm}]
     |  definedInStmt(_) default is set of []
    } in {
      exported = definedInStmt
    }

  private
  fun showCanonSeq([],_) is []
   |  showCanonSeq([P],S) is [S(P)]
   |  showCanonSeq([P,..R],S) is [S(P),ppStr(";"),ppNl,..showCanonSeq(R,S)]

  private
  fun showStmt(S) is switch(S) in {
    case canonDef(_,A,Vr,Vl) is ppSequence(0,[ppDisp(A),ppStr("def"),ppSpace,showPtn(Vr,1199),ppStr(":"),ppDisp(Vr.tipe),ppSpace,ppStr("is"),ppSpace,showExp(Vl,1199)])
    case canonVar(_,A,Vr,Vl) is ppSequence(0,[ppDisp(A),ppStr("var"),ppSpace,showPtn(Vr,1199),ppStr(":"),ppDisp(Vr.tipe),ppSpace,ppStr(":="),ppSpace,showExp(Vl,1199)])
    case canonAlgegraic(_,A,Tp,Cns) is ppSequence(0,[ppDisp(A),ppStr("type"),ppSpace,ppDisp(Tp),ppSpace,ppStr("is"),ppSpace,..showAlgebraicDef(Cns)])
    case canonContract(_,A,Nm,Tp,Sp,_) is ppSequence(0,[ppDisp(A),ppStr("contract"),ppSpace,ppDisp(Tp),ppSpace,ppStr("is"),ppSpace,ppDisp(Sp)])
    case canonImplementation(_,A,CTp,Sp) is ppSequence(0,[ppDisp(A),ppStr("implementation"),ppSpace,ppDisp(CTp),ppSpace,ppStr("is"),ppDisp(Sp)])
  }

  private
  fun showAlgebraicDef(Cns) is let {
    fun deQ(Tp) where stripQuants(Tp,(),(_,St)=>St,(_,St)=>St) matches (Stp,_) is Stp
    fun showCon(Nm,Tp) where deQ(Tp) matches iConTp(Lhs,_) is ppSequence(0,[ppStr(Nm),showType(Lhs,0)])
  } in interleave(cons of {all showCon(Nm,CnTp) where Nm->CnTp in Cns},ppStr("or"))

  -- Canonical expression term
  type cExp is 
       cVar{loc has type srcLoc; tipe has type iType; name has type string}   -- a variable of some form
    or cMethod{loc has type srcLoc; tipe has type iType; con has type iType;name has type string}   -- a method in a contract
    or cDeRef{loc has type srcLoc; tipe has type iType; deref has type cExp}  -- dereference a variable
    or cInt{loc has type srcLoc; tipe has type iType; ival has type integer}
    or cFloat{loc has type srcLoc; tipe has type iType; fval has type float}
    or cString{loc has type srcLoc; tipe has type iType; sval has type string}
    or cTuple{loc has type srcLoc; tipe has type iType; elements has type list of cExp}
    or cFace{loc has type srcLoc; tipe has type iType; values has type dictionary of (string,cExp);types has type dictionary of (string,iType)}
    or cField{loc has type srcLoc; tipe has type iType; record has type cExp; field has type string}
    or cApply{loc has type srcLoc; tipe has type iType; op has type cExp; arg has type cExp}
    or cSwitch{loc has type srcLoc; tipe has type iType; sel has type cExp; cases has type list of ((cPtn,boolean,cExp))}
    or cLet{loc has type srcLoc;tipe has type iType;env has type dict;stmts has type list of canonStmt;bnd has type cExp}
    or cLambda{loc has type srcLoc; tipe has type iType; lhs has type cPtn; rhs has type cExp}
    or cPttrn{loc has type srcLoc; tipe has type iType; value has type cExp; ptrn has type cPtn}
    or cMemo{loc has type srcLoc; tipe has type iType; value has type cExp}
    or cIsTrue{loc has type srcLoc; tipe has type iType; cond has type cCond}

  implementation pPrint over cExp is {
    ppDisp = shw
  } using {
    fun shw(E) is ppSequence(0,[showExp(E,2000),ppSpace,ppStr(":"),ppSpace,showType(E.tipe,2000),ppStr("@"),ppDisp(E.loc)])
  }

  private
  fun showExp(E,Pr) is switch E in {
    case cVar{name=Nm} is ppStr(Nm)
    case cMethod{name=Nm} is ppSequence(0,[ppStr(Nm),ppStr("©")])
    case cDeRef{deref=C} is parenthesize(ppSequence(0,[ppStr("!"),showExp(C,149)]),Pr>=150)
    case cInt{ival=Ix} is ppStr(Ix as string)
    case cFloat{fval=Dx} is ppStr(Dx as string)
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
    case cLambda{lhs=Args;rhs=Exp} is parenthesize(ppSequence(0,[
            showPtn(Args,909),ppSpace,ppStr("=>"),ppSpace,showExp(Exp,910)]),Pr>=910)
    case cPttrn{value=Exp;ptrn=Ptn} is parenthesize(ppSequence(0,[
            showExp(Exp,910),ppSpace,ppStr("from"),ppSpace,showPtn(Ptn,909)]),Pr>=910)
    case cMemo{value=Exp} is parenthesize(ppSequence(0,[ppStr("memo"),ppSpace,showExp(Exp,998)]),Pr>=999)
    case cLet{stmts=Stmts;bnd=B} is parenthesize(ppSequence(0,[
            ppStr("let"),ppSpace,ppStr("{"),ppNl,ppSequence(2,showCanonSeq(Stmts,showStmt)),ppNl,ppStr("}"),
                ppSpace,ppStr("in"),ppSpace,showExp(B,907)]),Pr>=908)
    case cSwitch{cases=Cs;sel=S} is parenthesize(ppSequence(0,[
          ppStr("switch"),ppSpace,showExp(S,907),ppSpace,ppStr("in"),ppSpace,ppStr("{"),ppNl,
                ppSequence(2,showCases(Cs,showExpCase)),ppNl,ppStr("}")]),Pr>=908)
    case cIsTrue{cond=C} is ppDisp(C)
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
  fun showExpCase(P,false,E) is ppSequence(0,[ppStr("case"),ppSpace,
          showPtn(P,1290),ppSpace,ppStr("is"),ppSpace,showExp(E,1289)])
   |  showExpCase(P,true,E) is ppSequence(0,[ppStr("case"),ppSpace,
          showPtn(P,1290),ppSpace,ppStr("default"),ppSpace,ppStr("is"),ppSpace,showExp(E,1289)])

  -- Canonical pattern term
  type cPtn is 
       pVar{loc has type srcLoc; tipe has type iType; name has type string} -- a new variable
    or pInt{loc has type srcLoc; tipe has type iType; ival has type integer}
    or pFloat{loc has type srcLoc; tipe has type iType; fval has type float}
    or pString{loc has type srcLoc; tipe has type iType; sval has type string}
    or pExp{loc has type srcLoc; tipe has type iType; val has type cExp}
    or pTuple{loc has type srcLoc; tipe has type iType; elements has type list of cPtn}
    or pFace{loc has type srcLoc; tipe has type iType; 
              values has type dictionary of (string,cPtn); types has type dictionary of (string,iType)}
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
    case pFloat{fval=Dx} is ppStr(Dx as string)
    case pString{sval=Sx} is ppSequence(0,cons of [ ppStr("\""), ppStr(Sx), ppStr("\"")])
    case pExp{val=Ex} is ppDisp(Ex)
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
    case pWhere{ptrn=Ptn;cond=Guard} is parenthesize(ppSequence(0,[
            showPtn(Ptn,939),ppSpace,ppStr("where"),ppSpace,showCond(Guard,939)]),Pr>=940)
    case pApply{op=Op;arg=Args} is ppSequence(0,[showExp(Op,0),parenthesize(showPtn(Args,0),Args matches pTuple{})])
  }

  implementation isExported over cPtn is let{
    fun ptnExport(P,soFar) is switch P in {
      case pVar{loc=Lc;tipe=Tp;name=N} is add_element(soFar,cVar{loc=Lc;tipe=Tp;name=N})
      case _ default is soFar
      case pTuple{elements=Tpl} is rightFold(ptnExport,soFar,Tpl)
      case pFace{values=Values} is rightFold(((_,V),S)=>ptnExport(V,S),soFar,Values)
      case pWhere{ptrn=Ptn} is ptnExport(Ptn,soFar)
      case pApply{arg=Args} is ptnExport(Args,soFar)
    }
  } in {
    fun exported(P) is ptnExport(P,set of [])
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

  implementation hasLocation over cCond is {
    fun locOf(E) is E.loc
  }

  implementation isExported over cCond is {
    exported = condExport
  } using {
    fun condExport(C) is switch C in {
      case cAnd{lhs=L; rhs=R} is condExport(L) union condExport(R)
      case cOr{lhs=L;rhs=R} is condExport(L) union condExport(R)
      case cNot{rhs=R} is condExport(R)
      case cImplies{lhs=L;rhs=R} is condExport(L) union condExport(R)
      case cOtherwise{lhs=L;rhs=R} is condExport(L) union condExport(R)
      case cCond{tst=T;lhs=L;rhs=R} is condExport(T) union condExport(L) union condExport(R)
      case cSearch{gen=G} is exported(G)
      case cIxSearch{gen=G;key=K} is exported(G) union exported (K)
      case _ default is set of []
    }
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
  
  private
  fun interSemi(0,_) is ppSpace
   |  interSemi(_,0) is ppSpace
   |  interSemi(_,_) default is ppStr(";")

  private 
  fun parenthesize(E,true) is E
   |  parenthesize(E,false) is ppSequence(0,[ppStr("("), E, ppStr(")")])

  -- Dictionary - is both a compiler artifact and a canonical artifact

  type typeEntry is typeIs{
    loc has type srcLoc
    tipe has type iType
  } or algebraicEntry{
    loc has type srcLoc
    tipe has type iType
    constructors has type list of string
  } or typeAlias{
    loc has type srcLoc
    tipe has type iType
    al has type iType
  }

  implementation hasLocation over typeEntry is {
    fun locOf(E) is E.loc
  }

  fun showTypeEntry(Nm,typeIs{tipe=Tp},D) is 
      ppSequence(0,[ppStr("type"),ppSpace,ppStr(Nm),ppSpace,ppStr("is"),ppSpace,ppDisp(Tp),ppNl])
   |  showTypeEntry(Nm,algebraicEntry{tipe=Tp;constructors=C},D) is 
      ppSequence(0,[ppStr("type"),ppSpace,ppDisp(Tp),ppSpace,ppStr("is"),ppSpace,ppDisp(C),ppNl])

  type varEntry is varEntry{
    loc has type srcLoc
    proto has type cExp
  }

  fun showVarEntry(Nm,varEntry{proto=Proto}) is 
      ppSequence(0,[ppStr(Nm),ppSpace,ppStr("has type"),showType(Proto.tipe,1999),ppNl])

  implementation hasLocation over varEntry is {
    fun locOf(E) is E.loc
  }

  type contractEntry is contractEntry{
    loc has type srcLoc
    tipe has type iType
    spec has type iType
    methods has type dictionary of (string,iType)
  }

  fun showContractEntry(Nm,contractEntry{tipe=Tp;spec=Spec},D) is
    ppSequence(0,[ppStr("contract"),ppSpace,showType(Tp,1199),ppSpace,ppStr("is"),ppSpace,showType(Spec,1199),ppNl])

  implementation hasLocation over contractEntry is {
    fun locOf(E) is E.loc
  }

  type implEntry is implEntry{
    loc has type srcLoc
    tipe has type iType
    implName has type string
  }

  implementation hasLocation over implEntry is {
    fun locOf(E) is E.loc
  }

  implementation pPrint over implEntry is {
    ppDisp = showImplementation
  }

  fun showImplementation(implEntry{tipe=Tp;implName=Nm}) is
      ppSequence(0,[ppStr("implementation"),ppSpace,ppDisp(Tp),ppSpace,ppStr(Nm),ppNl])

  type dict is dict{
    names has type dictionary of (string, varEntry)
    types has type dictionary of (string, typeEntry)
    contracts has type dictionary of (string, contractEntry)
    implementations has type dictionary of (string,implEntry)
    outer has type option of dict
  }

 implementation pPrint over dict is {
    fun ppDisp(D) is showDict(D,true)
  } 

  fun stackDict(D) is dict{
    names=dictionary of [];
    types = dictionary of [];
    contracts = dictionary of [];
    implementations=dictionary of [];
    outer=some(D)
  }

  private fun findInDict(Dict, local) is let {
    fun find(D) where local(D) has value X is some(X)
     |  find(dict{outer = O}) where O has value OD is find(OD)
     |  find(_) default is none
  } in find(Dict)

  fun findType(Dict,Nm) is findInDict(Dict, (dict{types=T}) => T[Nm])
  fun findVar(Dict,Nm) is findInDict(Dict, (dict{names=N})=>N[Nm])
  fun findContract(Dict,Nm) is findInDict(Dict, (dict{contracts=C})=>C[Nm])
  fun findImplementation(Dict,Nm) is findInDict(Dict, (dict{implementations=C})=>C[Nm])

  fun declareVar(Dict,Nm,Ve) is Dict substitute { names = Dict.names[with Nm->Ve]}
  fun declareType(Dict,Nm,Te) is Dict substitute { types = Dict.types[with Nm->Te]}

  fun freshVar(Lc,cVar{tipe=Tp;name=Nm}) is cVar{loc=Lc;tipe=freshen(Tp);name=Nm}
   |  freshVar(Lc,cMethod{tipe=Tp;name=Nm;con=Con}) is valof{
        def (mT,mQ) is freshenForUse(Tp,dictionary of [])
        def (mC,_) is freshenForUse(Con,mQ) -- this is a hack to ensure we actually have the right contract
        valis cMethod{loc=Lc;name=Nm;tipe=mT;con=mC}
      }

  fun declareContract(Dict,Nm,E) is valof {
    var D := Dict substitute { contracts = Dict.contracts[with Nm->E]}
      for K->T in E.methods do {
        def (conTipe,_) is stripQuants(E.tipe,(),(_,St)=>St,(_,St)=>St)
        D := defineVar(D,K,cMethod{loc=E.loc;name=K;tipe=T;con=conTipe})
      }
    valis D
  }

  fun declareImplementation(Dict,Lc,conTp) where implName(conTp) has value implNm is 
      Dict substitute { implementations = Dict.implementations[with implNm->implEntry{loc=Lc;tipe=conTp;implName=implNm}]};

  fun showDict(D,deep) is let{
    fun showTypes() is 
      ppSequence(2,cons of {all showTypeEntry(Nm,Tp,D) where Nm->Tp in D.types})
    fun showContracts() is
      ppSequence(2,cons of {all showContractEntry(Nm,C,D) where Nm->C in D.contracts})
    fun showNames() is 
      ppSequence(2,cons of {all showVarEntry(Nm,C) where Nm->C in D.names})
    fun showImplementations() is
      ppSequence(2,cons of {all showImplementation(I) where I in D.implementations})
    def showOuter is deep and D.outer has value Outer ? showDict(Outer,deep) : ppStr("")
  } in 
    ppSequence(0,cons of [showTypes(),showContracts(),showImplementations(),showNames(),showOuter])

  defineVar has type (dict,string,cExp) => dict
  fun defineVar(Dict,Nm,Proto) is Dict substitute {names = Dict.names[with Nm->varEntry{loc=Proto.loc;proto=Proto}]}

  defineConstructor has type (dict,srcLoc,string,iType) => dict
  fun defineConstructor(Dict,Lc,Nm,Tp) is Dict substitute {names = Dict.names[with Nm->varEntry{loc=Lc;proto=cVar{loc=Lc;tipe=Tp;name=Nm}}]}

  introduceType has type (dict,srcLoc,string,iType)=>dict
  fun introduceType(Dict,Lc,Nm,Tp) is declareType(Dict,Nm,typeIs{loc=Lc;tipe=Tp})

  fun typeOfField(Dict,algebraicEntry{constructors=Cons},Nm) is valof{
    for C in Cons and findVar(Dict,C) has value varEntry{proto=Proto} do {
      if preCheck(Proto.tipe,Nm) and findFieldInCon(freshen(Proto.tipe),Nm) has value Tp then {
        valis some(Tp)
      }
    }
    valis none
  }

  declareAlgebraic has type (dict,srcLoc,string,iType,dictionary of (string,iType))=>dict
  fun declareAlgebraic(Dict,Lc,Nm,Tp,Cons) is valof{
    var D := declareType(Dict,Nm,algebraicEntry{loc=Lc;tipe=Tp;constructors=list of { all Ky where  Ky->_ in Cons}})
    for Ky->ConTp in Cons do
      D := defineConstructor(D,Lc,Ky,ConTp)
    valis D
  }

  private
  fun preCheck(iUniv(_,T),Nm) is preCheck(T,Nm)
   |  preCheck(iExists(_,T),Nm) is preCheck(T,Nm)
   |  preCheck(iConstrained(T,_),Nm) is preCheck(T,Nm)
   |  preCheck(iConTp(L,R),Nm) is preCheck(L,Nm)
   |  preCheck(iFace(L,R),Nm) is present L[Nm] or present R[Nm]
   |  preCheck(_,_) default is false

  fun findFieldInCon(iConTp(L,R),Nm) is findFieldInCon(L,Nm)
   |  findFieldInCon(iFace(L,_),Nm) is L[Nm]
   |  findFieldInCon(_,_) default is none

  fun generalizeType(Tp,D) is generalize(Tp,(T)=>occCheck(T,D))

  private fun occCheck(iTvar{id=i;name=name;constraints=c},D) is let{
      fun check(dict{types=Tps}) where typeIs{tipe=Tp} in Tps and occursIn(i,Tp) is some(true)
       |  check(dict{names=Vrs}) where varEntry{proto=Proto} in Vrs and occursIn(i,Proto.tipe) is some(true)
       |  check(_) default is none
  } in (findInDict(D,check) has value X ? X : false)

  fun intersectDict(D1,D2) is D1 -- temporary definition
}