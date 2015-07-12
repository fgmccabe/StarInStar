check is package{
  -- type checker
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

  type errorMsg is alias of (string,srcLoc)

  type expTypePlugin is alias of ((ast,iType,dict,dict) => good of (canon,errorMsg))

  pkgType has type (ast,dict) => good of (canon,errorMsg)
  fun pkgType(isEquation(Lc,Lhs,isLblRecord(_,asName(_,"package"),Contents)),D) is typeOfRecord(Contents,typeVar(),D,D)

  typeOfExp has type (ast,iType,dict,dict) => good of (canon,errorMsg)
  fun typeOfExp(asName(Lc,Nm),E,D,O) is typeOfVar(Nm,Lc,E,D)
   |  typeOfExp(asInteger(Lc,I),E,D,O) is verifyType(Lc,iType("integer"),E,D,O,()=>good(expr{tipe=E;loc=Lc;exp=cInt(I)}))
   |  typeOfExp(asLong(Lc,Lx),E,D,O) is verifyType(Lc,iType("long"),E,D,O,()=>good(expr{tipe=E;loc=Lc;exp=cLong(Lx)}))
   |  typeOfExp(asFloat(Lc,Dx),E,D,O) is verifyType(Lc,iType("float"),E,D,O,()=>good(expr{tipe=E;loc=Lc;exp=cFloat(Dx)}))
   |  typeOfExp(asDecimal(Lc,Dx),E,D,O) is verifyType(Lc,iType("decimal"),E,D,O,()=>good(expr{tipe=E;loc=Lc;exp=cDecimal(Dx)}))
   |  typeOfExp(asChar(Lc,Cx),E,D,O) is verifyType(iType(Lc,"char"),E,D,O,()=>good(expr{tipe=E;loc=Lc;exp=cChar(Cx)}))
   |  typeOfExp(asString(Lc,Sx),E,D,O) is verifyType(Lc,iType("string"),E,D,O,()=>good(expr{tipe=E;loc=Lc;exp=cString(Sx)}))
   |  typeOfExp(asTuple(Lc,"()",list of [V]),E,D,O) is valof{
      	if V matches asTuple(_,"()",A) then -- only unwrap one paren
      	  valis typeOfTuple(Lc,A,E,D,O)
      	else
      		valis typeOfExp(V,E,D,O)
      }
   |  typeOfExp(asTuple(Lc,"()",A),E,D,O) is typeOfTuple(Lc,A,E,D,O)
   |  typeOfExp(asTuple(Lc,"{}",A),E,D,O) is typeOfRecord(Lc,A,E,D,O)
--   |  typeOfExp(asTuple(Lc,"[]",A),E,D,O) is typeOfSequence(Lc,A,E,D,O)
   |  typeOfExp(T matching asTuple(Lc,Nm,A),E,D,O) where expPlugins[(Nm,size(A))] has value plugin is plugin(T,E,D,O)
   |  typeOfExp(T matching asApply(Lc,asName(_,Nm),asTuple(_,"()",A)),E,D,O) where expPlugins[(Nm,size(A))] has value plugin is plugin(T,E,D,O)
   |  typeOfExp(T matching asApply(Lc,F,A),E,D,O) is valof{
      	def argType is typeVar()
      	def funType is iFnTp(argType,E)

      	switch typeOfExp(F,funType,D,O) in {
      	  case good(op) do 
      	  	switch typeOfExp(A,argType,D,O) in {
      	  	  case good(Arg) do
      	  	  	valis good(expr{tipe=E;loc=Lc;exp=cApply(op,Arg)})
      	  	  case noGood((M,aLc)) do
      	  	  	valis noGood(("$A not consistent argument of $F\nbecause #M",aLc))
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

  var expPlugins := dictionary of [
  	("ref",1)->typeOfReference,
    ("!",1)->typeOfShriek,
    ("=>",2)->typeOfLambda
/*    ("<=",2)->typeOfPttrn,
    ("memo",1)->typeOfMemo,
    ("do",2)->typeOfProc,
    (".",2)->typeOfFieldAccess,
    ("substitute",2)->typeOfSubstitute,
    ("and",2)->typeOfCond,
    ("or",2)->typeOfCond,
    ("not",1)->typeOfCond,
    ("otherwise",2)->typeOfCond,
    ("implies",2)->typeOfCond,
    ("case",1)->typeOfCase,
    ("let",1)->typeOfLet,
    ("in",2)->typeOfSearchPred,
    ("!=",2)->typeOfNotEquals,
    ("as",2)->typeOfCoerce,
    ("has type",2)->typeOfAnnotated,
    ("valof",1)->typeOfValof,
    ("computation",2)->typeOfComputation,
    ("of",2)->typeOfSequence,
    ("|",2)->typeOfConditional,
    ("or else",2)->typeOfDefault,
    ("@",2)->typeOfApply
    */
    ]

  prc installExpPlugin(name,arity,plugin) do {
    expPlugins[(name,arity)] := plugin
  }

  private
  fun typeOfReference(asApply(Lc,asName(_,"ref"),asTuple(_,_,list of [V])),E,D,O) is lvalueType(V,E,D,O)
   |  typeOfReference(T,E,D,O) default is noGood(("$T is not a reference term",locOf(T)))

  private
  fun typeOfShriek(asApply(Lc,asName(_,"!"),asTuple(_,_,list of [V])),E,D,O) is 
      	switch typeOfExp(V,iRfTp(E),D,O) in {
      	  case good(Ref) is good(expr{tipe=E;loc=Lc;exp=cDeRef(Ref)})
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
      	  	  case good(Ptn) do
                switch typeOfExp(R,resType,D,O) in {
      	  	      case good(Res) do
      	  	    	 valis good(expr{tipe=E;loc=Lc;exp=cLambda(Ptn,Res)})
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
                valis good(expr{tipe=E;loc=Lc;exp=cMemo(Ex)})
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
  fun typeOfNotEquals(asApply(Lc,asName(_,"!="),asTuple(_,_,list of [L,R])),E,D,O) is typeOfExp(unary(Lc,"not",bin(Lc,"=",L,R)),E,D,O)
   |  typeOfNotEquals(T,E,D,O) default is noGood(("$T is not a valid inequality",locOf(T)))

	private
  fun typeOfTuple(Lc,A,E,D,O) is valof{
        def elTypes is map((_)=>typeVar(),A)

        switch subsume(D)(E,iTuple(elTypes)) in {
          case noGood(M) do {
            valis noGood(("tuple not consistent with expected type $E\nbecause #M",Lc))
          }
          case good(_) do {
          	switch elMap((el,elT)=>typeOfExp(el,elT,D,O),A,elTypes,list of []) in {
          	  case good(els) do 
            		valis good(expr{loc=Lc;tipe=E;exp=cTuple(els)})
            	case noGood(M) do
          			valis noGood(M)
          	}
          }
        }
      }

  fun elMap(Fn,list of [],_,soFar) is good(soFar)
   |  elMap(Fn,list of [E,..R],list of [Et,..Rt],soFar) is switch Fn(E,Et) in {
        case good(X) is elMap(Fn,R,Rt,list of [soFar..,X])
        case noGood(M) is noGood(M)
      }

  fun typeOfRecord(Lc,A,E,D,O) where isThetaContents(A) is thetaContents(Lc,A,E,D)
   |  typeOfRecord(Lc,A,E,D,O) is valof{
      	def elTypes is dictionary of {all Nm->eTp where El in A and ((El matches isEqual(_,isIden(_,Nm),Rhs) and
                                                                      typeVar() matches eTp) or 
      	                                                         (El matches isAssignment(_,isIden(_,Nm),Rhs) and 
                                                                  iRfTp(typeVar()) matches eTp))}
      	def typeEls is dictionary of {all Nm->parseType(eTp,D) where isTypeAsignment(_,isIden(_,Nm),eTp) in A }

      	switch subsume(D)(E,iFace(elTypes,typeEls)) in {
      	  case noGood(M) do {
      	    valis noGood(("record not consistent with expected type $E\nbecause #M",Lc))
      	  }
      	  case good(_) do {
      	  	def els is dictionary of {all Nm->Exp where El in A and 
      	  	        ((El matches isEqual(_,isIden(_,Nm),Rhs) and typeOfExp(Rhs,someValue(elTypes[Nm]),D,O) has value Exp) or
      	  	         (El matches isAssignment(_,isIden(_,Nm),Rhs) and typeOfExp(Rhs,someValue(elTypes[Nm]),D,O) has value Exp))}

      	  	valis good(expr{loc=Lc;tipe=E;exp=cFace(els,typeEls)})
      	  }
      	}
      }

  private
  fun isThetaContents(A) is not ( El in A implies (El matches isEqual(_,_,_) 
                                            or El matches isAssignment(_,_,_)
                                            or El matches isTypeAssignment(_,_,_)))

  fun thetaContents(Lc,A,E,D) is 

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

  fun typeOfVar(Nm,Lc,E,D) where findVar(D,Nm) has value varEntry{ tipe = Tp} is valof {
    switch subsume(D)(E,freshenForUse(Tp)) in {
      case noGood(M) do 
        valis noGood(("$Nm not consistent with expected type $E\nbecause #M",Lc))
      case good(_) do 
        valis good(expr{loc=Lc;tipe=E;exp=cVar(Nm)})
    }
  }

  typeOfPtn has type (ast,iType,dict,dict) => good of (canon,errorMsg)
  fun typeOfPtn(asName(Lc,Nm),E,D,O) is typeOfPtnVar(Nm,Lc,E,D)
   |  typeOfPtn(asInteger(Lc,I),E,D,O) is verifyType(Lc,iType("integer"),E,D,O,()=>good(pttrn{tipe=E;loc=Lc;pttrn=pInt(I)}))
   |  typeOfPtn(asLong(Lc,Lx),E,D,O) is verifyType(Lc,iType("long"),E,D,O,()=>good(pttrn{tipe=E;loc=Lc;pttrn=pLong(Lx)}))
   |  typeOfPtn(asFloat(Lc,Dx),E,D,O) is verifyType(Lc,iType("float"),E,D,O,()=>good(pttrn{tipe=E;loc=Lc;pttrn=pFloat(Dx)}))
   |  typeOfPtn(asDecimal(Lc,Dx),E,D,O) is verifyType(Lc,iType("decimal"),E,D,O,()=>good(pttrn{tipe=E;loc=Lc;pttrn=pDecimal(Dx)}))
   |  typeOfPtn(asChar(Lc,Cx),E,D,O) is verifyType(iType(Lc,"char"),E,D,O,()=>good(pttrn{tipe=E;loc=Lc;pttrn=pChar(Cx)}))
   |  typeOfPtn(asString(Lc,Sx),E,D,O) is verifyType(Lc,iType("string"),E,D,O,()=>good(pttrn{tipe=E;loc=Lc;pttrn=pString(Sx)}))
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
  fun typeOfTuplePtn(Lc,A,E,D,O) is valof{
        def elTypes is map((_)=>typeVar(),A)

        switch subsume(D)(E,iTuple(elTypes)) in {
          case noGood(M) do {
            valis noGood(("tuple not consistent with expected type $E\nbecause #M",Lc))
          }
          case good(_) do {
            switch elMap((el,elT)=>typeOfPtn(el,elT,D,O),A,elTypes,list of []) in {
              case good(els) do 
                valis good(pttrn{loc=Lc;tipe=E;pttrn=pTuple(els)})
              case noGood(M) do
                valis noGood(M)
            }
          }
        }
      }

  private
  fun typeOfGuardedPtn(asApply(Lc,asName(_,"where"),asTuple(_,_,list of [P,C])),E,D,O) is valof{
      switch typeOfPtn(P,E,D,O) in {
        case good(GP) do {
          switch typeOfCond(C,D,O) in {
            case good(GC) do
              valis good(pttrn{tipe=E;loc=Lc;pttrn=pWhere(GP,GC)})
            case noGood(M) do
              valis noGood(M)
          }
        }
        case noGood(M) do
          valis noGood(M)
      }
    }

  var ptnPlugins := dictionary of [
    ("ref",1)->typeOfReferencePtn,
    ("where",2) -> typeOfGuardedPtn
/*    ("has type",2)->typeOfAnnotated,
    ("of",2)->typeOfSequencePtn,
    ("@",2)->typeOfApplyPtn
    */
    ]

  prc installPtnPlugin(name,arity,plugin) do {
    ptnPlugins[(name,arity)] := plugin
  }

  typeOfCond has type (ast,dict,dict) => good of (canon,errorMsg)
  fun typeOfCond(T matching asApply(Lc,asName(_,Nm),asTuple(_,"()",A)),D,O) where condPlugins[(Nm,size(A))] has value plugin is 
      plugin(T,D,O)
   |  typeOfCond(T,D,O) is typeOfExp(T,iType("boolean"),D,O)

  var condPlugins := dictionary of [
    ("and",2) -> typeOfConjunction,
    ("or",2) -> typeOfDisjunction,
    ("not",1) -> typeOfNegation,
    ("implies",2) -> typeOfImplies,
    ("otherwise",2) -> typeOfOtherwise,
    ("in",2) -> typeOfSearch,
    (":",2) -> typeOfConditional
    ]

  prc installCondlugin(name,arity,plugin) do {
    condPlugins[(name,arity)] := plugin
  }

  fun typeOfConjunction(asApply(Lc,asName(_,"and"),asTuple(_,"()",[L,R])),D,O) is valof{
    switch typeOfCond(L,D,O) in {
      case good(LL) do 
        switch typeOfCond(R,D,O) in {
          case good(RR) do
            valis good(cond{loc=Lc;cond=cAnd(LL,RR)})
          case noGood(M) do
            valis noGood(M)
        }
      case noGood(M) do
        valis noGood(M)
    }
  }

  fun typeOfDisjunction(asApply(Lc,asName(_,"or"),asTuple(_,"()",[L,R])),D,O) is valof{
    switch typeOfCond(L,D,O) in {
      case good(LL) do 
        switch typeOfCond(R,D,O) in {
          case good(RR) do
            valis good(cond{loc=Lc;cond=cOr(LL,RR)})
          case noGood(M) do
            valis noGood(M)
        }
      case noGood(M) do
        valis noGood(M)
    }
  }

  fun typeOfNegation(asApply(Lc,asName(_,"not"),asTuple(_,"()",[R])),D,O) is valof{
    switch typeOfCond(R,D,O) in {
      case good(RR) do
        valis good(cond{loc=Lc;cond=cNot(RR)})
      case noGood(M) do
        valis noGood(M)
    }
  }

  fun typeOfImplies(asApply(Lc,asName(_,"implies"),asTuple(_,"()",[L,R])),D,O) is valof{
    switch typeOfCond(L,D,O) in {
      case good(LL) do 
        switch typeOfCond(R,D,O) in {
          case good(RR) do
            valis good(cond{loc=Lc;cond=cImplies(LL,RR)})
          case noGood(M) do
            valis noGood(M)
        }
      case noGood(M) do
        valis noGood(M)
    }
  }

  fun typeOfOtherwise(asApply(Lc,asName(_,"otherwise"),asTuple(_,"()",[L,R])),D,O) is valof{
    switch typeOfCond(L,D,O) in {
      case good(LL) do 
        switch typeOfCond(R,D,O) in {
          case good(RR) do
            valis good(cond{loc=Lc;cond=cOtherwise(LL,RR)})
          case noGood(M) do
            valis noGood(M)
        }
      case noGood(M) do
        valis noGood(M)
    }
  }

  fun typeOfConditional(asApply(Lc,asName(_,":"),asTuple(_,"()",[asApply(_,asName(_,"?"),asTuple(_,"()",[T,L])),R])),D,O) is valof{
        switch typeOfCond(T,D,O) in {
          case good(TT) do 
            switch typeOfCond(L,D,O) in {
              case good(LL) do 
                switch typeOfCond(R,D,O) in {
                  case good(RR) do
                    valis good(cond{loc=Lc;cond=cCond(TT,LL,RR)})
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
              case good(KK) do 
                switch typeOfPtn(V,vlType,D,O) in {
                  case good(VV) do
                    valis good(cond{loc=Lc;cond=cIxSearch(KK,VV,SX)})
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
              case good(PP) do 
                valis good(cond{loc=Lc;cond=cSearch(PP,SX)})
              case noGood(M) do
                valis noGood(M)
            }
          }
          case noGood(M) do
            valis noGood(M)
        }  
      }
}