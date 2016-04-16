subsume is package{
  private import types
  private import canonical
  private import location
  private import good
  private import contracts
  private import freshen

  private type reset is resetVar(iType,integer)

  subsume has type (dict,srcLoc) => (iType,iType)=>good of ()
  fun subsume(D,Lc) is let{
    var resets := list of []
    var resetLevel := 0

    sub has type (iType,iType,iType,iType)=>good of ()
    fun sub(t1,v1,t2,v2) is switch (v1,v2) in {
      case (iBvar(Id),iBvar(Id)) is good(())
      case (iTvar{},_) is bindVar(v1,v2,sub)
      case (_,iTvar{}) is bindVar(v2,v1,super);
      case (iKvar(Nm,Or),iKvar(Nm,Or)) is good(());
      case (iType(Nm),iType(Nm)) is good(());
      case (iTuple(L1),iTuple(L2)) is size(L1)=size(L2) ?
          subList(L1,L2,sub) 
        : noGood("arity of $t1 different to arity of $t2",Lc);
      case (iFace(M1,T1),iFace(M2,T2)) is subFace(M1,T1,M2,T2);
      case (iFnTp(A1,R1),iFnTp(A2,R2)) is both(checkSub(A2,A1),()=>checkSub(R1,R2));
      case (iFnTp(A1,R1),iConTp(A2,R2)) is both(checkSub(A2,A1),()=>checkSub(R1,R2));
      case (iPtTp(A1,R1),iPtTp(A2,R2)) is both(checkSub(A1,A2),()=>checkSub(R2,R1));
      case (iPtTp(A1,R1),iConTp(A2,R2)) is both(checkSub(A1,A2),()=>checkSub(R2,R1));
      case (iConTp(A1,R1),iConTp(A2,R2)) is both(checkSame(A1,A2),()=>checkSame(R1,R2));
      case (iRfTp(A1),iRfTp(A2)) is checkSame(A1,A2);
      case (iTpExp(C1,A1),iTpExp(C2,A2)) is both(checkSub(C1,C2),()=>checkSub(A1,A2));
      case (iContract(Nm,A1,D1),iContract(Nm,A2,D2)) is size(A1)=size(A2) and size(D1)=size(D2) ?
          both(subList(A1,A2,sub),()=>subList(D1,D2,sub)) :
          noGood("arity of $t1 different to arity of $t2",Lc)
      case (iUniv(_,_),_) is valof{
      	def (f1,_) is freshenForUse(v1)
      	valis sub(f1,deRef(f1),t2,v2)
      };
      case (_,iUniv(_,_)) is valof{
      	def (f2,_) is freshenForEvidence(v2)
      	valis sub(t1,v1,f2,deRef(f2))
      };
      case (iExists(_,_),_) is valof{
      	def (e1,_) is freshenForUse(v1)
      	def mark is size(resets)
      	def Rslt is sub(e1,deRef(e1),t2,v2)
      	resetToMark(mark)
      	valis Rslt
      };
      case (_,iExists(_,_)) is valof{
      	def (e2,_) is freshenForEvidence(v2)
      	def mark is size(resets)
      	def Rslt is sub(t1,v1,e2,deRef(e2))
      	resetToMark(mark)
      	valis Rslt
      };
      case (_,_) default is 
      	noGood("$t1 not consistent with $t2",Lc)
    }

    fun super(t1,v1,t2,v2) is sub(t2,v2,t1,v1)

    fun subList(list of [],list of [],_) is good(())
     |  subList(list of [A1,..T1],list of [A2,..T2],S) is valof{
          def R is S(A1,deRef(A1),A2,deRef(A2))
          if R matches good(_) then
          	valis subList(T1,T2,S)
          else
          	valis R
        }

    fun subFace(M1,T1,M2,T2) is valof{
      if size(M1)>size(M2) then
      	valis noGood("$M2 has too few elements, compared to $M1",Lc)
      else{
      	for K->V1 in M1 do {
      	  if M2[K] has value V2 then {
      	    def R is sub(V1,deRef(V1),V2,deRef(V2))
      	    if not (R matches good(_)) then
      	      valis R
      	  } else
      	    valis noGood("$M2 does not contain entry for $K",Lc)
      	}
      	for K->V1 in T1 do{
      	  if T2[K] has value V2 then{
      	    def R is sub(V1,deRef(V1),V2,deRef(V2))
      	    if not (R matches good(_)) then
      	      valis R
      	  } else
      	    valis noGood("$T2 does not contain entry for $K",Lc)
      	}
      	valis good(())
      }
    }

    fun bindVar(V,T,S) is valof{
      if not T matches iTvar{} and occursIn(V.id,T) then
      	valis noGood("occurs check",Lc)
      else if T matches iTvar{id = Tid} and Tid = V.id then
        valis good(())
      else {
      	resets := list of [resetVar(V,resetLevel),..resets]
      	resetLevel := resetLevel+1
      	V.value := T
      	if T matches iTvar{} then
      	  valis mergeConstraints(T,V.constraints,S)
      	else
      	  valis checkConstraints(V.constraints,T,S)
      }
    }

    fun checkConstraints(list of [],_,_) is good(())
     |  checkConstraints(list of [C,..L],T,S) is 
          both((switch C in {
      	    case isOver(Cn) is checkContract(Cn,S)
      	    case hasField(Tp,Fld,FldTp) is checkFieldName(deRef(Tp),Fld,FldTp,S)
      	    case iTypeCon(_,Fld,FldTp) is good(())
      	    case hasKind(xT,K) is checkKind(deRef(xT),K)
      	    case instanceOf(iTp,jTp) is S(iTp,deRef(iTp),jTp,deRef(jTp))
      	    case isTuple(iTuple(_)) is good(())
            case isTuple(xT) is noGood("$xT is not a tuple type",Lc)
      	  }),()=>checkConstraints(L,T,S))

    fun checkContract(Cn,S) where implName(Cn) has value Nm is valof{
          if findImplementation(D,Nm) has value implEntry{tipe = iCn} then
            valis subContract(Cn,iCn,S)
          else
            valis noGood("$Cn not known to be implemented",Lc)
        }
     |  checkContract(_,_) is good(()) -- will be checked eventually

    fun subContract(iContract(Nm,LA,LD),iContract(Nm,RA,RD),S) is
          both(subList(LA,RA,S),()=>subList(LD,RD,S))
     |  subContract(L,R,_) is noGood("$L not consistent with $R",Lc)

    fun checkFieldName(iType(Nm),Field,FieldTp,S) where findType(D,Nm) has value Cons is
          typeOfField(D,Cons,Field) has value Ftp ?
            S(Ftp,deRef(Ftp),FieldTp,deRef(FieldTp)) :
            noGood("$Nm does not have a field $Field",Lc)
     |  checkFieldName(Tp,Field,FieldTp,S) default is noGood("$Tp not known to have field $Field",Lc)

    fun checkKind(iType(Nm),K) where findType(D,Nm) has value Desc is 
      switch Desc in {
        case typeIs{tipe=iT} is checkForm(evidence(iT),K)
        case algebraicEntry{tipe=iT} is checkForm(evidence(iT),K)
--        case typeAlias(iF) where iF(iType(Nm)) has value aTp is checkKind(aTp,K)
        case _ default is noGood("$Nm not a $K type",Lc)
      }

    fun checkForm(iType(_),kType) is good(())
     |  checkForm(_,kUnknown) is good(())
     |  checkForm(iTpExp(_,iTuple(L)),kTypeFun(Ix)) where size(L)=Ix is good(())
     |  checkForm(Tp,K) default is noGood("$Tp is not a $K type",Lc)

    fun mergeConstraints(T,list of [],_) is good(())
     |  mergeConstraints(T,list of [C,..L],S) is both(mergeConstraint(T,C,S),()=>mergeConstraints(T,L,S))

    fun mergeConstraint(T,C,S) is valof{
      T.constraints := list of [C,..T.constraints] -- fix me. Actually check the constraint
      valis good(())
    }

    fun chainLength(v) is valof{
      var V := v
      var len := 0
      while V matches iTvar{} do {
      	len := len+1
      	V := V.value
      }
      valis len
    }

    fun both(good(_),F) is F()
     |  both(R,_) is R

    fun checkSub(S,T) is valof{
      switch sub(S,deRef(S),T,deRef(T)) in {
      	case good(_) do valis good(())
      	case noGood(R,L) default do {
      	  resetToMark(0)
      	  valis noGood(R,L)
      	}
      }
    }

    fun checkSame(L,R) is both(checkSub(L,R),()=>checkSub(R,L))

    prc resetToMark(Tgt) do {
      while resets matches list of [resetVar(V,Lvl),..Rs] and Lvl>Tgt do{
      	V.value := unTyped
      	resets := Rs
      }
    }
  } in checkSub
}