check is package{
  private import good
  private import ast
  private import astUtils
  private import canonical
  private import subsume
  private import parseType
  private import stdTypes
  private import freshen
  private import typeUtils
  private import dependencies
  private import access
  private import flatmap
  private import (trace)

  typeOfProgram has type (ast,dict) => good of canonProgram
  fun typeOfProgram(isPackage(Lc,Nm,Body),D) is good computation {
    def pkgRecord is valof thetaRecord(Lc,Body,typeVar(),D)
    def pkgType is pkgRecord.tipe

    valis canonPackage{
      loc = Lc;
      name = Nm;
      imports = dictionary of [];
      pkg = cMemo{loc=Lc;tipe=iFnTp(iTuple([]),pkgType);value=pkgRecord };
    }
  }

  type expTypePlugin is alias of ((ast,iType,dict,dict) => good of cExp)

  pkgType has type (ast,dict) => good of cExp
  fun pkgType(isEquation(Lc,Lhs,isLabeledRecord(_,isIden(_,"package"),Contents)),D) is typeOfRecord(Lc,Contents,typeVar(),D,D)

  typeOfExp has type (ast,iType,dict,dict) => good of cExp
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
      	  	switch typeOfArguments(A,argType,D,O) in {
      	  	  case good(Arg) do
      	  	  	valis good(cApply{tipe=E;loc=Lc;op=op;arg=Arg})
      	  	  case noGood(M,aLc) do
      	  	  	valis noGood("$A not consistent arguments of $op\nbecause #M",aLc)
      	  	}
      	  case noGood(M,fLc) do 
      	    valis noGood("$F is not a function\nbecause #M",fLc)
      	}
      }
   |  typeOfExp(T,E,D,O) is noGood("Cannot understand expression $T",locOf(T))

  fun typeOfArguments(asTuple(Lc,"()",A),E,D,O) is typeOfTuple(Lc,A,E,D,O)
   |  typeOfArguments(X,E,D,O) is typeOfExp(X,E,D,O)

  fun lvalueType(V,E,D,O) is
    switch subsume(D,locOf(V))(E,iRfTp(typeVar())) in {
      case good(_) is
        typeOfExp(V,E,D,O)
      case noGood(M,Lc) is 
        noGood("$V not valid target of assignment\nbecause #M",Lc)
    }

  var expPlugins := dictionary of []

  prc installExpPlugin(name,arity,plugin) do {
    expPlugins[(name,arity)] := plugin
  }

  private
  fun typeOfVar(Nm,Lc,E,D) where findVar(D,Nm) has value varEntry{ tipe = Tp} is valof {
        switch subsume(D,Lc)(E,freshen(Tp)) in {
          case noGood(M,_) do 
            valis noGood("$Nm not consistent with expected type $E\nbecause #M",Lc)
          case good(_) do 
            valis good(cVar{loc=Lc;tipe=E;name=Nm})
        }
      }
   |  typeOfVar(Nm,Lc,E,F) is noGood("$Nm not declared",Lc)

  private
  fun typeOfReference(asApply(Lc,asName(_,"ref"),asTuple(_,_,list of [V])),E,D,O) is lvalueType(V,E,D,O)
   |  typeOfReference(T,E,D,O) default is noGood("$T is not a reference term",locOf(T))

  private
  fun typeOfShriek(asApply(Lc,asName(_,"!"),asTuple(_,_,list of [V])),E,D,O) is 
      	switch typeOfExp(V,iRfTp(E),D,O) in {
      	  case good(Ref) is good(cDeRef{tipe=E;loc=Lc;deref=Ref})
      		case noGood(M,eLc) default is noGood(M,eLc)
      	}
   |  typeOfShriek(T,E,D,O) default is noGood("$T is not a dereference term",locOf(T))

  private
  fun typeOfLambda(asApply(Lc,asName(_,"=>"),asTuple(_,_,list of [P,R])),E,D,O) is valof{
        def argType is typeVar()
        def resType is typeVar()

      	switch subsume(D,Lc)(E,iFnTp(argType,resType)) in {
      	  case good(_) do {
      	  	switch typeOfArgPtns(P,argType,D,O) in {
      	  	  case good((Ptn,lmDict)) do
                switch typeOfExp(R,resType,lmDict,O) in {
      	  	      case good(Res) do
      	  	    	 valis good(cLambda{tipe=E;loc=Lc;lhs=Ptn;rhs=Res})
      	  	      case noGood(M,rLc) do 
      	  	    	 valis noGood("value $R of lambda not consistent\nbecause #M",rLc)
      	  	    }
      	  	  case noGood(M,pLc) do
      	  	    valis noGood("pattern $P of lambda not consistent\nbecause #M",pLc)
      	  	}
      	  }
      	  case noGood(M,_) do
      	  	valis noGood("function not valid here\nbecause #M",Lc)
      	}
      }
   |  typeOfLambda(T,E,D,O) default is noGood("$T is not a valid lambda",locOf(T))

  private
  fun typeOfMemo(asApply(Lc,asName(_,"memo"),asTuple(_,_,list of [M])),E,D,O) is valof {
        def resType is typeVar()

        switch subsume(D,Lc)(E,iFnTp(iTuple([]),resType)) in {
          case good(_) do {
            switch typeOfExp(M,resType,D,O) in {
              case good(Ex) do
                valis good(cMemo{tipe=E;loc=Lc;value=Ex})
              case RR default do
                valis RR
            }
          }
          case noGood(RR,_) default do 
            valis noGood("memo not valid\nbecause #RR",Lc)
        }
      }
   |  typeOfMemo(T,E,D,O) default is noGood("$T not a valid memo expression",locOf(T))

	private
  fun typeOfTuple(Lc,A,E,D,O) is valof{
    def elTypes is map((_)=>typeVar(),A)

    switch subsume(D,Lc)(E,iTuple(elTypes)) in {
      case noGood(M,_) do {
        valis noGood("tuple $A not consistent with expected type $E\nbecause #M",Lc)
      }
      case good(_) do {
      	switch elMap((el,elT,soF)=>more(typeOfExp(el,elT,D,O),(XX)=>good(list of [soF..,XX])),A,elTypes,list of []) in {
      	  case good(els) do 
        		valis good(cTuple{loc=Lc;tipe=E;elements=els})
        	case noGood(M,_) do
      			valis noGood(M,Lc)
      	}
      }
    }
  }

  private
  fun elMap(Fn,list of [],_,soFar) is good(soFar)
   |  elMap(Fn,list of [E,..R],list of [Et,..Rt],soFar) is switch Fn(E,Et,soFar) in {
        case good(nX) is elMap(Fn,R,Rt,nX)
        case noGood(M,Lc) is noGood(M,Lc)
      }

  fun typeOfRecord(Lc,A,E,D,O) where isThetaContents(A) is thetaRecord(Lc,A,E,D)
   |  typeOfRecord(Lc,A,E,D,O) is good computation {
      	def elTypes is dictionary of {all Nm->eTp where El in A and ((El matches isEqual(_,isIden(_,Nm),Rhs) and
                                                                      typeVar() matches eTp) or 
      	                                                         (El matches isAssignment(_,isIden(_,Nm),Rhs) and 
                                                                  iRfTp(typeVar()) matches eTp))}

      	def typeEls is valof goodFilter(A,(() from isTypeAssignment(_,_,_)), 
              (isTypeAssignment(_,Nm,eTp))=>more(parseType(eTp,D),(pTp)=>good((Nm,pTp))))

        logMsg(info,"type elements: $typeEls")

      	switch subsume(D,Lc)(E,iFace(elTypes,typeEls)) in {
      	  case noGood(M,_) do abort with ("record not consistent with expected type $E\nbecause #M",Lc)
      	  case good(_) do {
      	  	def els is dictionary of {all Nm->Exp where El in A and 
      	  	        ((El matches isEqual(_,isIden(_,Nm),Rhs) and 
                      typeOfExp(Rhs,someValue(elTypes[Nm]),D,O) matches good(Exp)) or
      	  	         (El matches isAssignment(_,isIden(_,Nm),Rhs) and 
                      typeOfExp(Rhs,someValue(elTypes[Nm]),D,O) matches good(Exp)))}

      	  	valis cFace{loc=Lc;tipe=E;values=els;types=typeEls}
      	  }
      	}
      }

  private
  fun typeOfLet(isLetTerm(Lc,Body,Bnd),E,D,O) is 
    more(thetaContents(Body,D),((thDict,Stmts))=>
              more(typeOfExp(Bnd,E,thDict,O),(bndExp)=>good(cLet{loc=Lc;tipe=E;env=thDict;stmts=Stmts;bnd=bndExp})))

  private
  fun thetaContents(Defs,Dct) is let {
    groups has type list of astGroup
    def groups is dependencies(Defs)

    fun varCheck(LLc,Lhs,Rhs,tmpDict,ThDict,Bldr) is good computation {
      def eType is typeVar()
      def (ptnType,pD) is valof typeOfPtn(Lhs,eType,tmpDict,ThDict)
      def valType is valof typeOfExp(Rhs,eType,pD,ThDict)

      valis (Bldr(LLc,ptnType,valType),pD)
    }

    fun funCheck(LLc,Access,Fn,Eqns,tmpDict,ThDict) is let{
      def lhsType is typeVar()
      def rhsType is typeVar()
      var funDict := tmpDict;

      -- construct the function type and the dictionary to interpret the equations
      def fnType is valof{
        if findVar(tmpDict,Fn) has value varEntry{tipe=T} then{
          def (fT,M) is freshenForEvidence(T)
          for tV->V in M do -- record the type vars in case explicitly mentioned in body of function
            funDict := declareType(funDict,tV,typeIs{loc=LLc;tipe=V})
          switch subsume(funDict,LLc)(iFnTp(lhsType,rhsType),fT) in {
            case good(_) do
              valis good(fT)
            case noGood(EM,_) do
              valis noGood(EM,LLc)
          }
        } else 
          valis good(iFnTp(lhsType,rhsType))
      }

      fun eqnType(isEquation(Lc,isWherePtn(_,asApply(_,_,Lhs),C),Rhs),soFar) is good computation {
          def (Args,pDict) is valof typeOfArgPtns(Lhs,lhsType,funDict,ThDict)
          def (Cond,cDict) is valof typeOfCond(C,pDict,ThDict)
          def Val is valof typeOfExp(Rhs,rhsType,cDict,ThDict)
          valis list of [soFar..,(pWhere{tipe=lhsType;loc=Lc;ptrn=Args;cond=Cond},false,Val)]
        }
       |  eqnType(isEquation(Lc,isDefault(_,asApply(_,_,Lhs)),Rhs),soFar) is good computation {
          def (Args,pDict) is valof typeOfArgPtns(Lhs,lhsType,funDict,ThDict)
          def Val is valof typeOfExp(Rhs,rhsType,pDict,ThDict)
          valis list of [soFar..,(Args,true,Val)]
       }
       |  eqnType(isEquation(Lc,asApply(_,_,Lhs),Rhs),soFar) is good computation {
          def (Args,pDict) is valof typeOfArgPtns(Lhs,lhsType,funDict,ThDict)
          def Val is valof typeOfExp(Rhs,rhsType,pDict,ThDict)
          valis list of [soFar..,(Args,false,Val)]
       }
    } in (good computation {
        def fT is valof fnType
        def Es is valof pipeFold((EqSt,E)=>more(EqSt,(Eqs)=>eqnType(E,Eqs)),good(list of []),Eqns)
        valis (canonDef(LLc,Access,pVar{loc=LLc;tipe=fT;name=Fn},
                            cLambda{loc=LLc;
                              lhs=pVar{loc=LLc;tipe=lhsType;name="_$"};
                              rhs=cSwitch{loc=LLc;tipe=rhsType;
                                sel=cVar{loc=LLc;tipe=lhsType;name="_$"};
                                cases=Es};
                              tipe=fT}),funDict)
      })

    fun implementationCheck(Lc,Access,Tp,Body,tmpDict,thDict) is good computation {
      logMsg(info,"Check implementation for $Tp in $Body")
      def (Nm,contractType) is valof parseContractSpec(Tp,tmpDict,dictionary of [])
      logMsg(info,"Contract type $contractType")

      if findContract(tmpDict,Nm) has value contractEntry{tipe=cTp;spec=spType} then {
        def iTuple([conTp,recType]) is freshen(spType)
        logMsg(info,"declared contract $conTp is $recType")

        switch subsume(tmpDict,Lc)(conTp,contractType) in {
          case good(_) do {
            logMsg(info,"subsumed type is $conTp, record type is $recType");
            def impl is valof typeOfExp(Body,recType,tmpDict,thDict)
            logMsg(info,"impl record is $impl")
            valis (canonImplementation(Lc,Access,conTp,impl),declareImplementation(tmpDict,Lc,conTp))
          }
          case noGood(eM,eLc) do {
            logMsg(info,"type $conTp does not subsume $contractType");
            abort with (eM,eLc)
          }
        }
      } else {
        logMsg(info,"cannot find contract spec for $Nm")
      }

      abort with ("not implemented",Lc)
    }

    fun phase0([],tmpDict) is good(tmpDict)
     |  phase0([E,..Grp],tmpDict) is 
          switch E in {
            case (Def,_,expsion,Vars) is 
              phase0(Grp,rightFold((V,Dc)=>defineVar(Dc,locOf(Def),V,typeVar()),tmpDict,Vars))
            case (D,_,tipe,Tps) is
              switch D in {
                case isAlgebraicTypeDef(ALc,TNm,Lhs,_) is 
                  more(typeTemplate(Lhs,tmpDict),
                    (TT)=>phase0(Grp,introduceType(tmpDict,ALc,TNm,TT)))
                case isContractDef(CLc,CNm,_,_) is
                  more(introduceContract(D,tmpDict),(nxDict)=>phase0(Grp,nxDict))
                case _ default is noGood("Cannot understand $D/$Tps in phase0",locOf(D))
              }
          }

    fun phaseI([],thDict,tmpDict,soFar) is good((tmpDict,soFar))
     |  phaseI([(Def, Access, expsion, Defnd),..rest],thDict,tmpDict,soFar) is good computation{
          def (el,d) is valof (switch Def in {
            case isDefDef(_,isEquation(Lc,Lhs,Rhs)) is 
              varCheck(Lc,Lhs,Rhs,tmpDict,thDict,(L,M,N)=>canonDef(L,Access,M,N))
            case isVarDef(Lc,isEquation(_,Lhs,Rhs)) is
              varCheck(Lc,Lhs,Rhs,tmpDict,thDict,(L,M,N)=>canonVar(L,Access,M,N))
            case isFunDef(Lc,Eqns) is
              more(definedFunName(Def),(Nm)=>funCheck(Lc,Access,Nm,Eqns,tmpDict,thDict))
            case isImplementation(Lc,Tp,Body) is
              implementationCheck(Lc,Access,Tp,Body,tmpDict,thDict)
            case _ default is noGood("cannot understand $Def",locOf(Def))
          })
          valis valof phaseI(rest,thDict,d,[soFar..,el])
        }
     | phaseI([(Def,Access,tipe,TpNms),..rest],thDict,tmpDict,soFar) is switch Def in {
        case isAlgebraicTypeDef(Lc,Tp,Lhs,Rhs) is valof {
          if findType(tmpDict,Tp) has value typeIs{tipe=Type} then {
            def (T,Q) is stripQuants(Type,dictionary of [],(Nm,Mp)=>Mp[with Nm->iBvar(Nm)],skolemize)

            def conLhs is astFold((soF,C)=>more(soF,
                (sF)=>more(parseConstructor(C,tmpDict,Q,T),
                  ((CNm,CLc,Ctp))=>good(list of [(CNm,CLc,rightFold(((K,_),conT)=>iUniv(K,conT),Ctp,Q)),..sF]))),
                good(list of []),"or",Rhs)
            valis more(conLhs,(conDefs)=>valof{
              def nxtDict is rightFold(((K,CLc,KT),D)=>defineConstructor(D,CLc,K,KT),tmpDict,conDefs)
              valis phaseI(rest,thDict,nxtDict,soFar)
            })
          } else
          valis noGood("Cannot find types associated with $TpNms",Lc)
        }
        case isContractDef(Lc,Nm,Tp,Body) is valof {
          if findContract(tmpDict,Nm) has value contractEntry{tipe=CTp;spec=CSpec} then {
              valis phaseI(rest,thDict,tmpDict,[soFar..,canonContract(Lc,Access,Nm,CTp,CSpec)])
          } else
          valis noGood("Cannot find contract associated with $Nm",Lc)
        }
      }

    fun phaseII([],thDict,soFar) is good((soFar,thDict))
     |  phaseII([cDef,..moreCanon],thDict,soFar) is 
          more(generalizeDef(cDef,thDict),((gDef,thDict1))=>phaseII(moreCanon,thDict1,list of [soFar..,gDef]))

    fun generalizeDef(canonVar(Lc,A,Ptn,Val),thDict) is good((canonVar(Lc,A,Ptn,Val),ptnVars(defineVar,thDict,Ptn)))
     |  generalizeDef(canonDef(Lc,A,Ptn,Val),thDict) is 
          good((canonDef(Lc,A,Ptn substitute { tipe = generalizeType(Ptn.tipe,thDict)},Val),
                                            ptnVars((D,VLc,N,T)=>defineVar(D,VLc,N,generalizeType(T,thDict)),thDict,Ptn)))
     |  generalizeDef(canonImplementation(Lc,A,Tp,Impl),thDict) is valof{
          def conTp is generalizeType(Tp,thDict)
          logMsg(info,"thDict after declaring $Tp is $(declareImplementation(thDict,Lc,conTp))")
          valis good((canonImplementation(Lc,A,conTp,Impl), declareImplementation(thDict,Lc,conTp)))
        }
     |  generalizeDef(canonContract(Lc,A,Nm,Tp,Sp),thDict) is good computation {
          logMsg(info,"generalizing contract: $Tp, spec: $Sp")
          def GTp is generalizeType(Tp,thDict)
          def GSpec is generalizeType(Sp,thDict)
          logMsg(info,"next dict is $(declareContract(thDict,Lc,Nm,GTp,GSpec))") 
          valis (canonContract(Lc,A,Nm,GTp,GSpec),declareContract(thDict,Lc,Nm,GTp,GSpec))
        }
    
    fun checkGroup(Grp,thDict) is good computation {
      def tmpDict is valof phase0(Grp,thDict)
      def (tDict,rawDefs) is valof phaseI(Grp,thDict,tmpDict,list of [])
      -- logMsg(info,"tDict = $tDict, rawDefs = $rawDefs")
      valis valof phaseII(rawDefs,tDict,list of [])
    }

    fun checkGroups(Grps,thDict) is let {
      fun cG([],soFar,rDict) is good((rDict,soFar))
       |  cG([Grp,..R],soFar,rDict) is _combine(checkGroup(Grp,rDict),
            ((grp,nxDict)) => cG(R,soFar++grp,nxDict))
      } in cG(Grps,list of [],thDict)
      
  } in checkGroups(groups,stackDict(Dct))

  private
  ptnVars has type ((dict,srcLoc,string,iType)=>dict,dict,cPtn)=>dict
  fun ptnVars(F,D,Pt) is switch Pt in {
    case pVar{loc=Lc;tipe = T; name = N} is F(D,Lc,N,T)
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

  fun thetaRecord(Lc,A,E,D) is good computation {
    def (thDict,Stmts) is valof thetaContents(A,D)
    def exports is reduction (union) of {all exported(S) where S in Stmts}
    def recType is sealType(Stmts)
    perform subsume(D,Lc)(E,recType)
    valis cLet {
      loc=Lc;
      tipe=recType;
      env=thDict;
      stmts=Stmts;
      bnd=sealRecord(Lc,recType,Stmts)
    }
  }

  fun sealType(Stmts) is let {
    fun collectField(canonDef(_,pUblic,P,_),iFace(Fields,Types)) is 
          iFace(leftFold((FD,cVar{name=VN;tipe=VT})=>FD[with VN->VT],Fields,exported(P)),Types)
     |  collectField(canonVar(_,pUblic,P,_),iFace(Fields,Types)) is 
          iFace(leftFold((FD,cVar{name=VN;tipe=VT})=>FD[with VN->VT],Fields,exported(P)),Types)
     |  collectField(canonAlgegraic(_,pUblic,Tp,Cons),iFace(Fields,Types)) where typeName(Tp) has value ATp is
          iFace(leftFold((FD,(K,T))=>FD[with K->T],Fields,Cons),Types[with ATp->Tp])
     |  collectField(Entry,Tp) is Tp trace "Ignoring statement $Entry in sealType"
  } in rightFold(collectField,iFace(dictionary of [],dictionary of []),Stmts)

  fun sealRecord(Lc,RecType,Stmts) is let {
      fun collectField(canonDef(_,pUblic,P,_),Rec) is 
          Rec substitute { values = leftFold((FD,V)=>FD[with V.name->V],Rec.values,exported(P)) }
     |  collectField(canonVar(_,pUblic,P,_),Rec) is 
          Rec substitute { values = leftFold((FD,V)=>FD[with V.name->V],Rec.values,exported(P)) }
     |  collectField(canonAlgegraic(_,pUblic,Tp,Cons),Rec) where typeName(Tp) has value ATp is
          Rec substitute { types = (Rec.types)[with ATp->Tp] } 
     |  collectField(Entry,Tp) is Tp trace "Ignoring statement $Entry in sealRecord"
  } in rightFold(collectField,cFace{loc=Lc;tipe=RecType;values=dictionary of [];types=dictionary of []},Stmts)

  fun verifyType(Lc,aTp,eTp,D,O,Succ) is valof {
    switch subsume(D,Lc)(eTp,aTp) in {
      case noGood(M,_) do {
        valis noGood("$aTp not consistent with expected type $eTp\nbecause #M",Lc)
      }
      case good(_) do {
        valis Succ()
      }
    }
  }

  typeOfPtn has type (ast,iType,dict,dict) => good of ((cPtn,dict))
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
   |  typeOfPtn(asTuple(Lc,"{}",A),E,D,O) is typeOfRecordPtn(Lc,A,E,D,O)
--   |  typeOfPtn(asTuple(Lc,"[]",A),E,D,O) is typeOfSequencePtn(Lc,A,E,D,O)
   |  typeOfPtn(isExpPtn(Lc,Exp),E,D,O) is more(typeOfExp(Exp,E,D,O),(EE)=>good((pExp{loc=Lc;tipe=E;val=EE},D)))
   |  typeOfPtn(T matching asTuple(Lc,Nm,A),E,D,O) where ptnPlugins[(Nm,size(A))] has value plugin is plugin(T,E,D,O)
   |  typeOfPtn(T matching asApply(Lc,asName(_,Nm),asTuple(_,"()",A)),E,D,O) where ptnPlugins[(Nm,size(A))] has value plugin is
        plugin(T,E,D,O)
   |  typeOfPtn(asApply(Lc,Op,A),E,D,O) is typeOfApplyPtn(Lc,Op,A,E,D,O)
   |  typeOfPtn(T,E,D,O) is noGood("Cannot understand pattern $T",locOf(T))

  private
  fun typeOfArgPtns(asTuple(Lc,"()",A),E,D,O) is typeOfTuplePtn(Lc,A,E,D,O)
   |  typeOfArgPtns(P,E,D,O) default is typeOfPtn(P,E,D,O)

  private
  fun typeOfPtnVar(Nm,Lc,E,D) where findVar(D,Nm) has value varEntry{ tipe = Tp} is valof {
        def varType is freshen(Tp)

        switch subsume(D,Lc)(varType,E) in {
          case noGood(M,_) do {
            valis noGood("$Nm not consistent with expected type $E\nbecause #M",Lc)
          }
          case good(_) do 
            valis good((pVar{loc=Lc;tipe=E;name=Nm},D))
        }
      }
   |  typeOfPtnVar(Nm,Lc,E,D) is good((pVar{loc=Lc;tipe=E;name=Nm},defineVar(D,Lc,Nm,E)))

  private
  fun typeOfTuplePtn(Lc,A,E,D,O) is valof{
    def elTypes is map((_)=>typeVar(),A)

    switch subsume(D,Lc)(E,iTuple(elTypes)) in {
      case noGood(M,_) do {
        valis noGood("pattern tuple $(asTuple(Lc,"()",A)) not consistent with expected type $E\nbecause #M",Lc)
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
            case noGood(M,Mlc) do {
              valis noGood("pattern tuple $(asTuple(Lc,"()",A)) not consistent with expected type $E\nbecause #M",Mlc)
            }
          }
        }

        valis good((pTuple{loc=Lc;tipe=E;elements=tupleEls},tupleD))
      }
    }
  }

  private
  fun typeOfApplyPtn(Lc,Op,A,E,D,O) is good computation {
    def aT is typeVar()
    def Tp is iPtTp(aT,E)
    def op is valof typeOfExp(Op,Tp,D,O)
    def (arg,argDict) is valof typeOfPtn(A,aT,D,O)
    valis (pApply{loc=Lc;tipe=E;op=op;arg=arg},argDict)
  }

  private
  fun typeOfRecordPtn(Lc,A,E,D,O) is good computation {
    def elTypes is dictionary of {all Nm->eTp where El in A and ((El matches isEqual(_,isIden(_,Nm),Rhs) and
                                                                      typeVar() matches eTp) or 
                                                                 (El matches isAssignment(_,isIden(_,Nm),Rhs) and 
                                                                  iRfTp(typeVar()) matches eTp))}
    def typeEls is valof goodIterate(A,(isTypeAssignment(_,Nm,eTp))=>more(parseType(eTp,D),(pTp)=>good((Nm,pTp))))

    switch subsume(D,Lc)(E,iFace(elTypes,typeEls)) in {
      case noGood(M,_) do abort with ("record not consistent with expected type $E\nbecause #M",Lc)
      case good(_) do {
        var ptnD := D
        var els := dictionary of []

        for El in A do{
          switch El in {
            case isEqual(_,isIden(_,Nm),Rhs) where elTypes[Nm] has value elType do {
              switch typeOfPtn(Rhs,elType,ptnD,O) in {
                case good((P,xD)) do {
                  els[Nm] := P
                  ptnD := xD
                }
                case noGood(M,mLc) do
                  abort with (M,mLc)
              }
            }
            case isAssignment(_,isIden(_,Nm),Rhs) where elTypes[Nm] has value iRfTp(elType) do {
              switch typeOfPtn(Rhs,elType,ptnD,O) in {
                case good((P,xD)) do {
                  els[Nm] := P
                  ptnD := xD
                }
                case noGood(M,mLc) do
                  abort with (M,mLc)
              }
            }
            case isTypeAssignment(_,Nm,Rhs) do {
              nothing
            }
          }
        }

        valis (pFace{loc=Lc;tipe=E;values=els;types=typeEls},ptnD)
      }
    }
  }

  private
  fun typeOfGuardedPtn(isWherePtn(Lc,P,C),E,D,O) is valof{
      switch typeOfPtn(P,E,D,O) in {
        case good((GP,nD)) do {
          switch typeOfCond(C,nD,O) in {
            case good((GC,oD)) do
              valis good((pWhere{tipe=E;loc=Lc;ptrn=GP;cond=GC},oD))
            case noGood(M,mLc) do
              valis noGood(M,mLc)
          }
        }
        case noGood(M,mLc) do
          valis noGood(M,mLc)
      }
    }

  var ptnPlugins := dictionary of []

  prc installPtnPlugin(name,arity,plugin) do {
    ptnPlugins[(name,arity)] := plugin
  }

  typeOfCond has type (ast,dict,dict) => good of ((cCond,dict))
  fun typeOfCond(T matching asApply(Lc,asName(_,Nm),asTuple(_,"()",A)),D,O) where condPlugins[(Nm,size(A))] has value plugin is 
      plugin(T,D,O)
   |  typeOfCond(T,D,O) is switch typeOfExp(T,iType("boolean"),D,O) in {
        case good(Ex) is good((cExp{loc=locOf(T);exp=Ex},D))
        case noGood(M,mLc) is noGood(M,mLc)
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
          case noGood(M,mLc) do
            valis noGood(M,mLc)
        }
      case noGood(M,mLc) do
        valis noGood(M,mLc)
    }
  }

  fun typeOfDisjunction(asApply(Lc,asName(_,"or"),asTuple(_,"()",[L,R])),D,O) is valof{
    switch typeOfCond(L,D,O) in {
      case good((LL,lD)) do 
        switch typeOfCond(R,D,O) in {
          case good((RR,rD)) do
            valis good((cOr{loc=Lc;lhs=LL;rhs=RR},intersectDict(lD,rD)))
          case noGood(M,mLc) do
            valis noGood(M,mLc)
        }
      case noGood(M,mLc) do
        valis noGood(M,mLc)
    }
  }

  fun typeOfNegation(asApply(Lc,asName(_,"not"),asTuple(_,"()",[R])),D,O) is valof{
    switch typeOfCond(R,D,O) in {
      case good((RR,_)) do
        valis good((cNot{loc=Lc;rhs=RR},D))
      case noGood(M,mLc) do
        valis noGood(M,mLc)
    }
  }

  fun typeOfImplies(asApply(Lc,asName(_,"implies"),asTuple(_,"()",[L,R])),D,O) is valof{
    switch typeOfCond(L,D,O) in {
      case good((LL,lD)) do 
        switch typeOfCond(R,lD,O) in {
          case good((RR,_)) do
            valis good((cImplies{loc=Lc;lhs=LL;rhs=RR},D))
          case noGood(M,mLc) do
            valis noGood(M,mLc)
        }
      case noGood(M,mLc) do
        valis noGood(M,mLc)
    }
  }

  fun typeOfOtherwise(asApply(Lc,asName(_,"otherwise"),asTuple(_,"()",[L,R])),D,O) is valof{
    switch typeOfCond(L,D,O) in {
      case good((LL,lD)) do 
        switch typeOfCond(R,D,O) in {
          case good((RR,rD)) do
            valis good((cOtherwise{loc=Lc;lhs=LL;rhs=RR},intersectDict(lD,rD)))
          case noGood(M,mLc) do
            valis noGood(M,mLc)
        }
      case noGood(M,mLc) do
        valis noGood(M,mLc)
    }
  }

  fun typeOfConditional(isBinary(Lc,":",isBinary(_,"?",T,L),R),D,O) is valof{
        switch typeOfCond(T,D,O) in {
          case good((TT,lD)) do 
            switch typeOfCond(L,lD,O) in {
              case good((LL,llD)) do 
                switch typeOfCond(R,D,O) in {
                  case good((RR,rD)) do
                    valis good((cCond{loc=Lc;tst=TT;lhs=LL;rhs=RR},intersectDict(llD,rD)))
                  case noGood(M,mLc) do
                    valis noGood(M,mLc)
                }
              case noGood(M,mLc) do
                valis noGood(M,mLc)
            }
          case noGood(M,mLc) do
            valis noGood(M,mLc)
        }
      }
   |  typeOfConditional(T matching asApply(Lc,_,_),D,O) default is
        noGood("invalid form of conditional $T",Lc)

  fun typeOfSearch(isBinary(Lc,"in",isBinary(_,"->",K,V),S),D,O) is valof{
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
                  case noGood(M,mLc) do
                    valis noGood(M,mLc)
                }
                case noGood(M,mLc) do
                  valis noGood(M,mLc)
            }
          }
          case noGood(M,mLc) do
            valis noGood(M,mLc)
        }    
      }
   |  typeOfSearch(isBinary(Lc,"in",P,S),D,O) is valof{
        def elType is typeVar()
        def coType is contractConstrainedType("iterable",[elType])

        switch typeOfExp(S,coType,D,O) in {
          case good(SX) do {
            switch typeOfPtn(P,elType,D,O) in {
              case good((PP,pD)) do 
                valis good((cSearch{loc=Lc;gen=PP;src=SX},D))
              case noGood(M,mLc) do
                valis noGood(M,mLc)
            }
          }
          case noGood(M,mLc) do
            valis noGood(M,mLc)
        }  
      }
}