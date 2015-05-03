subsume is package{
  private import types;
  private import dict;
  private import location;
  private import good;
  private import freshen;

  private type reset is resetVar(iType,integer);

  subsume has type (dict) => (iType,iType)=>good of ();
  subsume(D) is let{
    var resets := list of [];
    var resetLevel := 0;

    sub has type (iType,iType,iType,iType)=>good of ()
    sub(t1,v1,t2,v2) is case (v1,v2) in {
      (iTvar{},iTvar{}) is bindVar(v1,v2);
      (iTvar{},_) is bindVar(v1,v2);
      (_,iTvar{}) is bindVar(v2,v1);
      (iKvar(Nm,Or),iKvar(Nm,Or)) is good(());
      (iType(Nm),iType(Nm)) is good(());
      (iTuple(L1),iTuple(L2)) is size(L1)=size(L2) ?
          subList(L1,L2) 
        | noGood("arity of $t1 different to arity of $t2");
      (iFace(M1,T1),iFace(M2,T2)) is subFace(M1,T1,M2,T2);
      (iFnTp(A1,R1),iFnTp(A2,R2)) is both(checkSub(A2,A1),fn ()=>checkSub(R1,R2));
      (iPtTp(A1,R1),iPtTp(A2,R2)) is both(checkSub(A1,A2),fn ()=>checkSub(R2,R1));
      (iRfTp(A1),iRfTp(A2)) is both(checkSub(A1,A2),fn ()=>checkSub(A2,A1));
      (iTpExp(C1,A1),iTpExp(C2,A2)) is both(checkSub(C1,C2),fn ()=>checkSub(A1,A2));
      (iUniv(_,_),_) is valof{
      	var f1 is freshenForUse(v1);
      	valis sub(f1,deRef(f1),t2,v2);
      };
      (_,iUniv(_,_)) is valof{
      	var f2 is freshenForEvidence(v2);
      	valis sub(t1,v1,f2,deRef(f2));
      };
      (iExists(_,_),_) is valof{
      	var e1 is freshenForUse(v1);
      	var mark is size(resets);
      	var Rslt is sub(e1,deRef(e1),t2,v2);
      	resetToMark(mark);
      	valis Rslt;
      };
      (_,iExists(_,_)) is valof{
      	var e2 is freshenForEvidence(v2);
      	var mark is size(resets);
      	var Rslt is sub(t1,v1,e2,deRef(e2));
      	resetToMark(mark);
      	valis Rslt;
      };
      (_,_) default is 
      	noGood("$t1 not consistent with $t2");
    };

    subList(list of [],list of []) is good(());
    subList(list of [A1,..T1],list of [A2,..T2]) is valof{
      var R is sub(A1,deRef(A1),A2,deRef(A2));
      if R matches good(_) then
      	valis subList(T1,T2)
      else
      	valis R
    }

    subFace(M1,T1,M2,T2) is valof{
      if size(M1)>size(M2) then
      	valis noGood("$M2 has too few elements, compared to $M1")
      else{
      	for K->V1 in M1 do {
      	  if M2[K] matches V2 then {
      	    var R is sub(V1,deRef(V1),V2,deRef(V2));
      	    if not (R matches good(_)) then
      	      valis R
      	  } else
      	    valis noGood("$M2 does not contain entry for $K")
      	};
      	for K->V1 in T1 do{
      	  if T2[K] matches V2 then{
      	    var R is sub(V1,deRef(V1),V2,deRef(V2));
      	    if not (R matches good(_)) then
      	      valis R
      	  } else
      	    valis noGood("$T2 does not contain entry for $K")
      	}
      	valis good(());
      }
    };

    bindVar(V,T) is valof{
      if occursIn(V.id,T) then
      	valis noGood("occurs check")
      else{
      	resets := list of [resetVar(V,resetLevel),..resets];
      	resetLevel := resetLevel+1;
      	V.value := T;
      	if T matches iTvar{} then
      	  valis mergeConstraints(T,V.constraints)
      	else
      	  valis checkConstraints(V.constraints,T);
      }
    };

    checkConstraints(list of [],_) is good(());
    checkConstraints(list of [C,..L],T) is 
      both((case C in {
  	    iContract(_,_,_) is good(()); -- fix me: check for implementations
  	    iFieldCon(_,Fld,FldTp) is good(());
  	    iTypeCon(_,Fld,FldTp) is good(());
  	    hasKind(_,K) is good(());
  	    instanceOf(_,iTp) is good(());
  	    isTuple(_) is good(());
  	  }),fn ()=>checkConstraints(L,T));

    mergeConstraints(T,list of []) is good(())
    mergeConstraints(T,list of [C,..L]) is both(mergeConstraint(T,C),fn ()=>mergeConstraints(T,L))

    mergeConstraint(T,C) is valof{
      T.constraints := list of [C,..T.constraints] -- fix me. Actually check the constraint
      valis good(())
    }


    chainLength(v) is valof{
      var V := v;
      var len := 0;
      while V matches iTvar{} do {
      	len := len+1;
      	V := V.value;
      }
      valis len
    };

    both(good(_),F) is F();
    both(R,_) is R;

    checkSub(S,T) is valof{
      case sub(S,deRef(S),T,deRef(T)) in {
      	good(_) do valis good(());
      	noGood(R) default do {
      	  resetToMark(0);
      	  valis noGood(R)
      	}
      }
    };

    resetToMark(Tgt) do {
      while resets matches list of [resetVar(V,Lvl),..Rs] and Lvl>Tgt do{
      	V.value := unTyped;
      	resets := Rs;
      }
    };
  } in fn(S,T) => checkSub(S,T);
}