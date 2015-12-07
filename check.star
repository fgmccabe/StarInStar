check is package{
  private import good
  private import errors
  private import ast
  private import astUtils
  private import canonical
  private import subsume
  private import dict
  private import parseType
  private import freshen
  private import typeUtils
  private import dependencies
  private import flatmap

  type errorMsg is alias of (string,srcLoc)

  type expTypePlugin is alias of ((ast,iType,dict,dict) => good of (cExp,errorMsg))

  pkgType has type (ast,dict) => good of (cExp,errorMsg)
  fun pkgType(isEquation(Lc,Lhs,isLblRecord(_,asName(_,"package"),Contents)),D) is typeOfRecord(Lc,Contents,typeVar(),D,D)

  typeOfExp has type (ast,iType,dict,dict) => good of (cExp,errorMsg)
  fun typeOfExp(asName(Lc,Nm),E,D,O) is typeOfVar(Nm,Lc,E,D)
   |  typeOfExp(asInteger(Lc,I),E,D,O) is verifyType(Lc,iType("integer"),E,D,O,()=>good(cInt{tipe=E;loc=Lc;ival=I}))
   |  typeOfExp(asLong(Lc,Lx),E,D,O) is verifyType(Lc,iType("long"),E,D,O,()=>good(cLong{tipe=E;loc=Lc;lval=Lx}))
   |  typeOfExp(asFloat(Lc,Dx),E,D,O) is verifyType(Lc,iType("float"),E,D,O,()=>good(cFloat{tipe=E;loc=Lc;fval=Dx}))
   |  typeOfExp(asDecimal(Lc,Dx),E,D,O) is verifyType(Lc,iType("decimal"),E,D,O,()=>good(cDecimal{tipe=E;loc=Lc;dval=Dx}))
   |  typeOfExp(asChar(Lc,Cx),E,D,O) is verifyType(Lc,iType("char"),E,D,O,()=>good(cChar{tipe=E;loc=Lc;cval=Cx}))
   |  typeOfExp(asString(Lc,Sx),E,D,O) is verifyType(Lc,iType("string"),E,D,O,()=>good(cString{tipe=E;loc=Lc;sval=Sx}))
   |  typeOfExp(asTuple(Lc,"()",list of [V]),E,D,O) is -- only unwrap one paren
      	V matches asTuple(_,"()",A) ? typeOfTuple(Lc,A,E,D,O) : typeOfExp(V,E,D,O)
   |  typeOfExp(asTuple(Lc,"()",A),E,D,O) is typeOfTuple(Lc,A,E,D,O)
   |  typeOfExp(asTuple(Lc,"{}",A),E,D,O) is typeOfRecord(Lc,A,E,D,O)
--   |  typeOfExp(asTuple(Lc,"[]",A),E,D,O) is typeOfSequence(Lc,A,E,D,O)
   |  typeOfExp(T matching isApply(Lc,Nm,A),E,D,O) where expPlugins[(Nm,size(A))] has value plugin is plugin(T,E,D,O)
   |  typeOfExp(T matching asApply(Lc,F,A),E,D,O) is valof{
      	def argType is typeVar()
      	def fnType is iFnTp(argType,E)

      	switch typeOfExp(F,fnType,D,O) in {
      	  case good(op) do 
      	  	switch typeOfExp(A,argType,D,O) in {
      	  	  case good(Arg) do
      	  	  	valis good(cApply{tipe=E;loc=Lc;op=op;arg=Arg})
      	  	  case noGood((M,aLc)) do
      	  	  	valis noGood(("$A not consistent arguments of $op\nbecause #M",aLc))
      	  	}
      	  case noGood((M,fLc)) do 
      	    valis noGood(("$F is not a function\nbecause #M",fLc))
      	}
      }
   |  typeOfExp(T,E,D,O) is noGood(("Cannot understand expression $T",locOf(T)))

  fun lvalueType(V,E,D,O) is
    switch subsume(D)(E,iRfTp(typeVar())) in {
      case good(_) is
        typeOfExp(V,E,D,O)
      case noGood(M) is 
        noGood(("$V not valid target of assignment\nbecause #M",locOf(V)))
    }

  var expPlugins := dictionary of []

  prc installExpPlugin(name,arity,plugin) do {
    expPlugins[(name,arity)] := plugin
  }

  private
  fun typeOfVar(Nm,Lc,E,D) where findVar(D,Nm) has value varEntry{ tipe = Tp} is valof {
    switch subsume(D)(E,freshen(Tp)) in {
      case noGood(M) do 
        valis noGood(("$Nm not consistent with expected type $E\nbecause #M",Lc))
      case good(_) do 
        valis good(cVar{loc=Lc;tipe=E;name=Nm})
    }
  }

  private
  fun typeOfReference(asApply(Lc,asName(_,"ref"),asTuple(_,_,list of [V])),E,D,O) is lvalueType(V,E,D,O)
   |  typeOfReference(T,E,D,O) default is noGood(("$T is not a reference term",locOf(T)))

  private
  fun typeOfShriek(asApply(Lc,asName(_,"!"),asTuple(_,_,list of [V])),E,D,O) is 
      	switch typeOfExp(V,iRfTp(E),D,O) in {
      	  case good(Ref) is good(cDeRef{tipe=E;loc=Lc;deref=Ref})
      		case noGood(M) default is noGood(M)
      	}
   |  typeOfShriek(T,E,D,O) default is noGood(("$T is not a dereference term",locOf(T)))

  private
  fun typeOfLambda(asApply(Lc,asName(_,"=>"),asTuple(_,_,list of [P,R])),E,D,O) is valof{
        def argType is typeVar()
        def resType is typeVar()

      	switch subsume(D)(E,iFnTp(argType,resType)) in {
      	  case good(_) do {
      	  	switch typeOfPtn(P,argType,D,O) in {
      	  	  case good((Ptn,lmDict)) do
                switch typeOfExp(R,resType,lmDict,O) in {
      	  	      case good(Res) do
      	  	    	 valis good(cLambda{tipe=E;loc=Lc;lhs=Ptn;rhs=Res})
      	  	      case noGood((M,rLc)) do 
      	  	    	 valis noGood(("value $R of lambda not consistent\nbecause #M",rLc))
      	  	    }
      	  	  case noGood((M,pLc)) do
      	  	    valis noGood(("pattern $P of lambda not consistent\nbecause #M",pLc))
      	  	}
      	  }
      	  case noGood(M) do
      	  	valis noGood(("function not valid here\nbecause #M",Lc))
      	}
      }
   |  typeOfLambda(T,E,D,O) default is noGood(("$T is not a valid lambda",locOf(T)))

  private
  fun typeOfMemo(asApply(Lc,asName(_,"memo"),asTuple(_,_,list of [M])),E,D,O) is valof {
        def resType is typeVar()

        switch subsume(D)(E,iFnTp(iTuple([]),resType)) in {
          case good(_) do {
            switch typeOfExp(M,resType,D,O) in {
              case good(Ex) do
                valis good(cMemo{tipe=E;loc=Lc;value=Ex})
              case RR default do
                valis RR
            }
          }
          case noGood(RR) default do 
            valis noGood(("memo not valid\nbecause #RR",Lc))
        }
      }
   |  typeOfMemo(T,E,D,O) default is noGood(("$T not a valid memo expression",locOf(T)))

	private
  fun typeOfTuple(Lc,A,E,D,O) is valof{
        def elTypes is map((_)=>typeVar(),A)

        switch subsume(D)(E,iTuple(elTypes)) in {
          case noGood(M) do {
            valis noGood(("tuple not consistent with expected type $E\nbecause #M",Lc))
          }
          case good(_) do {
          	switch elMap((el,elT,soF)=>more(typeOfExp(el,elT,D,O),(XX)=>good(list of [soF..,XX])),A,elTypes,list of []) in {
          	  case good(els) do 
            		valis good(cTuple{loc=Lc;tipe=E;elements=els})
            	case noGood(M) do
          			valis noGood(M)
          	}
          }
        }
      }

  private
  fun elMap(Fn,list of [],_,soFar) is good(soFar)
   |  elMap(Fn,list of [E,..R],list of [Et,..Rt],soFar) is switch Fn(E,Et,soFar) in {
        case good(nX) is elMap(Fn,R,Rt,nX)
        case noGood(M) is noGood(M)
      }

  fun typeOfRecord(Lc,A,E,D,O) where isThetaContents(A) is thetaRecord(Lc,A,E,D)
   |  typeOfRecord(Lc,A,E,D,O) is valof{
      	def elTypes is dictionary of {all Nm->eTp where El in A and ((El matches isEqual(_,isIden(_,Nm),Rhs) and
                                                                      typeVar() matches eTp) or 
      	                                                         (El matches isAssignment(_,isIden(_,Nm),Rhs) and 
                                                                  iRfTp(typeVar()) matches eTp))}
      	def typeEls is dictionary of {all Nm->parseType(eTp,D) where isTypeAssignment(_,isIden(_,Nm),eTp) in A }

      	switch subsume(D)(E,iFace(elTypes,typeEls)) in {
      	  case noGood(M) do {
      	    valis noGood(("record not consistent with expected type $E\nbecause #M",Lc))
      	  }
      	  case good(_) do {
      	  	def els is dictionary of {all Nm->Exp where El in A and 
      	  	        ((El matches isEqual(_,isIden(_,Nm),Rhs) and typeOfExp(Rhs,someValue(elTypes[Nm]),D,O) matches good(Exp)) or
      	  	         (El matches isAssignment(_,isIden(_,Nm),Rhs) and typeOfExp(Rhs,someValue(elTypes[Nm]),D,O) matches good(Exp)))}

      	  	valis good(cFace{loc=Lc;tipe=E;values=els;types=typeEls})
      	  }
      	}
      }

  private
  fun typeOfLet(isLetTerm(Lc,Body,Bnd),E,D,O) is 
    more(thetaContents(Body,D),((thDict,env))=>
              more(typeOfExp(Bnd,E,thDict,O),(bndExp)=>good(cLet{loc=Lc;tipe=E;env=env;bnd=bndExp})))

  private
  fun thetaContents(Defs,Dct) is let {
    groups has type list of astGroup
    def groups is dependencies(Defs)

    fun varCheck(LLc,Lhs,Rhs,tmpDict,ThDict,Bldr) is valof{
      def eType is typeVar()
      def ptnType is typeOfPtn(Lhs,eType,tmpDict,ThDict)
      def valType is typeOfExp(Rhs,eType,tmpDict,ThDict)

      valis more(ptnType,((P,vD))=>more(valType,(V)=>good((Bldr(LLc,P,V),vD))))
    }

    fun funCheck(LLc,Fn,Eqns,tmpDict,ThDict) is let{
      def lhsType is typeVar()
      def rhsType is typeVar()
      var funDict := tmpDict;

      -- construct the function type and the dictionary to interpret the equations
      def fnType is valof{
        if findVar(tmpDict,Fn) has value varEntry{tipe=T} then{
          def (fT,M) is freshenForEvidence(T)
          logMsg(info,"Var $Fn had type $T, freshened to $fT")
          for tV->V in M do -- record the type vars in case explicitly mentioned in body of function
            funDict := declareType(funDict,tV,typeIs(V))
          switch subsume(funDict)(iFnTp(lhsType,rhsType),fT) in {
            case good(_) do
              valis good(fT)
            case noGood(EM) do
              valis noGood((EM,LLc))
          }
        } else 
          valis good(iFnTp(lhsType,rhsType))
      }

      fun eqnType(isEquation(Lc,asApply(_,_,Lhs),Rhs),soFar) is valof{
        def eqnDict is funDict
        valis more(typeOfPtn(Lhs,lhsType,eqnDict,ThDict),((Args,pDict))=>
                        more(typeOfExp(Rhs,rhsType,pDict,ThDict),(Val)=>good(list of [soFar..,(Args,Val)])))
      }
    } in more(fnType,(fT)=>valof{
        def eqnTypes is pipeFold((EqSt,E)=>more(EqSt,(Eqs)=>eqnType(E,Eqs)),good(list of []),Eqns)
        valis more(eqnTypes,(Eqs)=>valof{
          def arg is pVar{loc=LLc;tipe=lhsType;name="_$"}
          valis good((canonDef(LLc,pVar{loc=LLc;tipe=fT;name=Fn},
                            cLambda{loc=LLc;lhs=arg;rhs=cSwitch{loc=LLc;tipe=rhsType;sel=cVar{loc=LLc;tipe=lhsType;name="_$"};
                                                          cases=Eqs};tipe=fT}),funDict))
          })
      })

    fun phase0([],tmpDict) is tmpDict
     |  phase0([(_,expsion,Vars),..rest],tmpDict) is 
          phase0(rest,rightFold((V,Dc)=>defineVar(Dc,V,typeVar()),tmpDict,Vars))

    fun phaseI([],thDict,tmpDict,soFar) is good((tmpDict,soFar))
     |  phaseI([(Def, Cat, Defnd),..rest],thDict,tmpDict,soFar) is valof{
          def item is switch Def in {
            case isDefDef(_,isEquation(Lc,Lhs,Rhs)) is 
              varCheck(Lc,Lhs,Rhs,tmpDict,thDict,(L,M,N)=>canonDef(L,M,N))
            case isVarDef(Lc,isEquation(_,Lhs,Rhs)) is
              varCheck(Lc,Lhs,Rhs,tmpDict,thDict,(L,M,N)=>canonVar(L,M,N))
            case isFunDef(Lc,Eqns) is
              more(definedFunName(Def),(Nm)=>funCheck(Lc,Nm,Eqns,tmpDict,thDict))
          }
          valis more(item,((el,d))=>phaseI(rest,thDict,d,[soFar..,el]))
        }
    fun phaseII([],thDict,soFar) is good((soFar,thDict))
     |  phaseII([cDef,..moreCanon],thDict,soFar) is 
          more(generalizeDef(cDef,thDict),((gDef,thDict1))=>phaseII(moreCanon,thDict1,list of [soFar..,gDef]))

    fun generalizeDef(canonVar(Lc,Ptn,Val),thDict) is good((canonVar(Lc,Ptn,Val),ptnVars(defineVar,thDict,Ptn)))
     |  generalizeDef(canonDef(Lc,Ptn,Val),thDict) is good((canonDef(Lc,Ptn substitute { tipe = generalizeType(Ptn.tipe,thDict)},Val),
                                                            ptnVars((D,N,T)=>defineVar(D,N,generalizeType(T,thDict)),thDict,Ptn)))
    
    fun checkGroup(Grp,thDict) is more(phaseI(Grp,Dct,phase0(Grp,thDict),list of []),
                              ((tmpDict,rawDefs))=>phaseII(rawDefs,thDict,list of []))

    fun checkGroups([Grp,..rest],thDict,soFar) is more(checkGroup(Grp,thDict),((grp,nxDict))=>checkGroups(rest,nxDict,soFar++grp)) 
     |  checkGroups([],thDict,soFar) is good((thDict,soFar))
  } in checkGroups(groups,Dct,list of [])

  private
  ptnVars has type ((dict,string,iType)=>dict,dict,cPtn)=>dict
  fun ptnVars(F,D,Pt) is switch Pt in {
    case pVar{tipe = T; name = N} is F(D,N,T)
    case _ default is D
    case pTuple{elements = V} is rightFold((E,St)=>ptnVars(F,St,E),D,V)
    case pFace{values = V} is rightFold(((_,E),St)=>ptnVars(F,St,E),D,V)
    case pWhere{ptrn = P} is ptnVars(F,D,P)
    case pApply{arg = A} is ptnVars(F,D,A)
  }

  private
  fun isThetaContents(A) is not ( El in A implies (El matches isEqual(_,_,_) 
                                            or El matches isAssignment(_,_,_)
                                            or El matches isTypeAssignment(_,_,_)))

  fun thetaRecord(Lc,A,E,D) is noGood(("not implemented ",Lc))

  fun verifyType(Lc,aTp,eTp,D,O,Succ) is valof {
    switch subsume(D)(eTp,aTp) in {
      case noGood(M) do {
        valis noGood(("$aTp not consistent with expected type $eTp\nbecause #M",Lc))
      }
      case good(_) do {
        valis Succ()
      }
    }
  }

  typeOfPtn has type (ast,iType,dict,dict) => good of ((cPtn,dict) ,errorMsg)
  fun typeOfPtn(asName(Lc,Nm),E,D,O) is typeOfPtnVar(Nm,Lc,E,D)
   |  typeOfPtn(asInteger(Lc,I),E,D,O) is verifyType(Lc,iType("integer"),E,D,O,()=>good((pInt{tipe=E;loc=Lc;ival=I},D)))
   |  typeOfPtn(asLong(Lc,Lx),E,D,O) is verifyType(Lc,iType("long"),E,D,O,()=>good((pLong{tipe=E;loc=Lc;lval=Lx},D)))
   |  typeOfPtn(asFloat(Lc,Dx),E,D,O) is verifyType(Lc,iType("float"),E,D,O,()=>good((pFloat{tipe=E;loc=Lc;fval=Dx},D)))
   |  typeOfPtn(asDecimal(Lc,Dx),E,D,O) is verifyType(Lc,iType("decimal"),E,D,O,()=>good((pDecimal{tipe=E;loc=Lc;dval=Dx},D)))
   |  typeOfPtn(asChar(Lc,Cx),E,D,O) is verifyType(Lc,iType("char"),E,D,O,()=>good((pChar{tipe=E;loc=Lc;cval=Cx},D)))
   |  typeOfPtn(asString(Lc,Sx),E,D,O) is verifyType(Lc,iType("string"),E,D,O,()=>good((pString{tipe=E;loc=Lc;sval=Sx},D)))
   |  typeOfPtn(asTuple(Lc,"()",list of [V]),E,D,O) is valof{
        if V matches asTuple(_,"()",A) then -- only unwrap one paren
          valis typeOfTuplePtn(Lc,A,E,D,O)
        else
          valis typeOfPtn(V,E,D,O)
      }
   |  typeOfPtn(asTuple(Lc,"()",A),E,D,O) is typeOfTuplePtn(Lc,A,E,D,O)
--   |  typeOfPtn(asTuple(Lc,"{}",A),E,D,O) is typeOfRecordPtn(Lc,A,E,D,O)
--   |  typeOfExp(asTuple(Lc,"[]",A),E,D,O) is typeOfSequencePtn(Lc,A,E,D,O)
   |  typeOfPtn(T matching asTuple(Lc,Nm,A),E,D,O) where ptnPlugins[(Nm,size(A))] has value plugin is plugin(T,E,D,O)
   |  typeOfPtn(T matching asApply(Lc,asName(_,Nm),asTuple(_,"()",A)),E,D,O) where ptnPlugins[(Nm,size(A))] has value plugin is plugin(T,E,D,O)
   |  typeOfPtn(T,E,D,O) is noGood(("Cannot understand pattern $T",locOf(T)))

  private
  fun typeOfPtnVar(Nm,Lc,E,D) where findVar(D,Nm) has value varEntry{ tipe = Tp} is valof {
        switch subsume(D)(freshen(Tp),E) in {
          case noGood(M) do 
            valis noGood(("$Nm not consistent with expected type $E\nbecause #M",Lc))
          case good(_) do 
            valis good((pVar{loc=Lc;tipe=E;name=Nm},D))
        }
      }
   |  typeOfPtnVar(Nm,Lc,E,D) is good((pVar{loc=Lc;tipe=E;name=Nm},defineVar(D,Nm,E)))

  private
  fun typeOfTuplePtn(Lc,A,E,D,O) is valof{
    def elTypes is map((_)=>typeVar(),A)

    switch subsume(D)(E,iTuple(elTypes)) in {
      case noGood(M) do {
        valis noGood(("tuple not consistent with expected type $E\nbecause #M",Lc))
      }
      case good(_) do {
        var tupleEls := list of []
        var tupleD := D

        for (Arg,ArgType) in zip(A,elTypes) do {
          switch typeOfPtn(Arg,ArgType,tupleD,O) in {
            case good((argPtn,argDict)) do {
              extend tupleEls with argPtn
              tupleD := argDict
            }
            case noGood((M,Mlc)) do {
              valis noGood(("tuple not consistent with expected type $E\nbecause #M",Lc))
            }
          }
        }

        valis good((pTuple{loc=Lc;tipe=E;elements=tupleEls},tupleD))
      }
    }
  }

  private
  fun typeOfGuardedPtn(asApply(Lc,asName(_,"where"),asTuple(_,_,list of [P,C])),E,D,O) is valof{
      switch typeOfPtn(P,E,D,O) in {
        case good((GP,nD)) do {
          switch typeOfCond(C,nD,O) in {
            case good((GC,oD)) do
              valis good((pWhere{tipe=E;loc=Lc;ptrn=GP;cond=GC},oD))
            case noGood(M) do
              valis noGood(M)
          }
        }
        case noGood(M) do
          valis noGood(M)
      }
    }

  var ptnPlugins := dictionary of []

  prc installPtnPlugin(name,arity,plugin) do {
    ptnPlugins[(name,arity)] := plugin
  }

  typeOfCond has type (ast,dict,dict) => good of ((cCond,dict),errorMsg)
  fun typeOfCond(T matching asApply(Lc,asName(_,Nm),asTuple(_,"()",A)),D,O) where condPlugins[(Nm,size(A))] has value plugin is 
      plugin(T,D,O)
   |  typeOfCond(T,D,O) is switch typeOfExp(T,iType("boolean"),D,O) in {
        case good(Ex) is good((cExp{loc=locOf(T);exp=Ex},D))
        case noGood(M) is noGood(M)
      }

  var condPlugins := dictionary of []

  {
    installExpPlugin("ref",1, typeOfReference)
    installExpPlugin("!",1, typeOfShriek)
    installExpPlugin("=>",2, typeOfLambda)
/*    installExpPlugin("<=",2, typeOfPttrn)
    installExpPlugin("memo",1, typeOfMemo)
    installExpPlugin("do",2, typeOfProc)
    installExpPlugin(".",2, typeOfFieldAccess)
    installExpPlugin("substitute",2, typeOfSubstitute)
    installExpPlugin("and",2, typeOfCond)
    installExpPlugin("or",2, typeOfCond)
    installExpPlugin("not",1, typeOfCond)
    installExpPlugin("otherwise",2, typeOfCond)
    installExpPlugin("implies",2, typeOfCond)
    installExpPlugin("switch",1, typeOfCase)
*/
    installExpPlugin("let",1, typeOfLet)
/*
    installExpPlugin("in",2, typeOfSearchPred)
    installExpPlugin("as",2, typeOfCoerce)
    installExpPlugin("has type",2, typeOfAnnotatedExp)
    installExpPlugin("valof",1, typeOfValof)
    installExpPlugin("computation",2, typeOfComputation)
    installExpPlugin("of",2, typeOfSequence)
    installExpPlugin("|",2, typeOfConditional)
    installExpPlugin("or else",2, typeOfDefault)
    installExpPlugin("@",2, typeOfApply)

*/
    installPtnPlugin("where",2,typeOfGuardedPtn)
    -- installPtnPlugin("ref",1,typeOfReferencePtn)
    -- installPtnPlugin("has type",2,typeOfAnnotatedPtn)
    -- installPtnPlugin("of",2,typeOfSequencePtn)
    -- installPtnPlugin("@",2,typeOfApplyPtn)

    installCondPlugin("and",2,typeOfConjunction)
    installCondPlugin("or",2,typeOfDisjunction)
    installCondPlugin("not",1,typeOfNegation)
    installCondPlugin("implies",2, typeOfImplies)
    installCondPlugin("otherwise",2, typeOfOtherwise)
    installCondPlugin("in",2, typeOfSearch)
    installCondPlugin(":",2,typeOfConditional)
  }

  prc installCondPlugin(name,arity,plugin) do {
    condPlugins[(name,arity)] := plugin
  }

  fun typeOfConjunction(asApply(Lc,asName(_,"and"),asTuple(_,"()",[L,R])),D,O) is valof{
    switch typeOfCond(L,D,O) in {
      case good((LL,nD)) do 
        switch typeOfCond(R,nD,O) in {
          case good((RR,oD)) do
            valis good((cAnd{loc=Lc;lhs=LL;rhs=RR},oD))
          case noGood(M) do
            valis noGood(M)
        }
      case noGood(M) do
        valis noGood(M)
    }
  }

  fun typeOfDisjunction(asApply(Lc,asName(_,"or"),asTuple(_,"()",[L,R])),D,O) is valof{
    switch typeOfCond(L,D,O) in {
      case good((LL,lD)) do 
        switch typeOfCond(R,D,O) in {
          case good((RR,rD)) do
            valis good((cOr{loc=Lc;lhs=LL;rhs=RR},intersectDict(lD,rD)))
          case noGood(M) do
            valis noGood(M)
        }
      case noGood(M) do
        valis noGood(M)
    }
  }

  fun typeOfNegation(asApply(Lc,asName(_,"not"),asTuple(_,"()",[R])),D,O) is valof{
    switch typeOfCond(R,D,O) in {
      case good((RR,_)) do
        valis good((cNot{loc=Lc;rhs=RR},D))
      case noGood(M) do
        valis noGood(M)
    }
  }

  fun typeOfImplies(asApply(Lc,asName(_,"implies"),asTuple(_,"()",[L,R])),D,O) is valof{
    switch typeOfCond(L,D,O) in {
      case good((LL,lD)) do 
        switch typeOfCond(R,lD,O) in {
          case good((RR,_)) do
            valis good((cImplies{loc=Lc;lhs=LL;rhs=RR},D))
          case noGood(M) do
            valis noGood(M)
        }
      case noGood(M) do
        valis noGood(M)
    }
  }

  fun typeOfOtherwise(asApply(Lc,asName(_,"otherwise"),asTuple(_,"()",[L,R])),D,O) is valof{
    switch typeOfCond(L,D,O) in {
      case good((LL,lD)) do 
        switch typeOfCond(R,D,O) in {
          case good((RR,rD)) do
            valis good((cOtherwise{loc=Lc;lhs=LL;rhs=RR},intersectDict(lD,rD)))
          case noGood(M) do
            valis noGood(M)
        }
      case noGood(M) do
        valis noGood(M)
    }
  }

  fun typeOfConditional(asApply(Lc,asName(_,":"),asTuple(_,"()",[asApply(_,asName(_,"?"),asTuple(_,"()",[T,L])),R])),D,O) is valof{
        switch typeOfCond(T,D,O) in {
          case good((TT,lD)) do 
            switch typeOfCond(L,lD,O) in {
              case good((LL,llD)) do 
                switch typeOfCond(R,D,O) in {
                  case good((RR,rD)) do
                    valis good((cCond{loc=Lc;tst=TT;lhs=LL;rhs=RR},intersectDict(llD,rD)))
                  case noGood(M) do
                    valis noGood(M)
                }
              case noGood(M) do
                valis noGood(M)
            }
          case noGood(M) do
            valis noGood(M)
        }
      }
   |  typeOfConditional(T matching asApply(Lc,_,_),D,O) default is
        noGood(("invalid form of conditional $T",Lc))

  fun typeOfSearch(asApply(Lc,asName(_,"in"),asTuple(_,"()",[asApply(_,asName(_,"->"),asTuple(_,"()",[K,V])),S])),D,O) is valof{
        def kyType is typeVar()
        def vlType is typeVar()
        def coType is contractConstrainedType("indexed_iterable",[kyType,vlType])

        switch typeOfExp(S,coType,D,O) in {
          case good(SX) do {
            switch typeOfPtn(K,kyType,D,O) in {
              case good((KK,pD)) do 
                switch typeOfPtn(V,vlType,pD,O) in {
                  case good((VV,vD)) do
                    valis good((cIxSearch{loc=Lc;key=KK;gen=VV;src=SX},D))
                  case noGood(M) do
                    valis noGood(M)
                }
                case noGood(M) do
                  valis noGood(M)
            }
          }
          case noGood(M) do
            valis noGood(M)
        }    
      }
   |  typeOfSearch(asApply(Lc,asName(_,"in"),asTuple(_,"()",[P,S])),D,O) is valof{
        def elType is typeVar()
        def coType is contractConstrainedType("iterable",[elType])

        switch typeOfExp(S,coType,D,O) in {
          case good(SX) do {
            switch typeOfPtn(P,elType,D,O) in {
              case good((PP,pD)) do 
                valis good((cSearch{loc=Lc;gen=PP;src=SX},D))
              case noGood(M) do
                valis noGood(M)
            }
          }
          case noGood(M) do
            valis noGood(M)
        }  
      }
}