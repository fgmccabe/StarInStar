subsume is package{
  private import types;
  private import dict;

  private type reset is resetVar(iType,integer);

  subsume has type (dict) => (iType,iType)=>result of ();
  subsume(D) is let{
    var resets := list of {};
    var resetLevel := 0;

    sub has type (iType,iType,iType,iType)=>result of ()
    sub(t1,v1,t2,v2) is case (v1,v2) in {
      (iTvar{},iTvar{}) is bindVar(v1,v2);
      (iTvar{},_) is bindVar(v1,v2);
      (_,iTvar{}) is bindVar(v2,v1);
      (iKvar(Nm,Or),iKvar(Nm,Or)) is success(());
      (iType(Nm,K),iType(Nm,K)) is success(());
      (iTuple(L1),iTuple(L2)) is size(L1)=size(L2) ?
          subList(L1,L2) 
        | failed("arity of $t1 different to arity of $t2");
      (iFace(M1,T1),iFace(M2,T2)) is subFace(M1,T1,M2,T2);
      (iFnTp(A1,R1),iFnTp(A2,R2)) is both(checkSub(A2,A1),fn ()=>checkSub(R1,R2));
      (iPtTp(A1,R1),iPtTp(A2,R2)) is both(checkSub(A1,A2),fn ()=>checkSub(R2,R1));
      (iRfTp(A1),iRfTp(A2)) is both(checkSub(A1,A2),fn ()=>checkSub(A2,A1));
      (iTpExp(C1,A1),iTpExp(C2,A2)) is both(checkSub(C1,C2),fn ()=>checkSub(A1,A2));
      (iUniv(_,_,_),_) is valof{
      	var f1 is freshenForUse(v1,D);
      	valis sub(f1,deRef(f1),t2,v2);
      };
      (_,iUniv(_,_,_)) is valof{
      	var f2 is freshenForEvidence(v2,D);
      	valis sub(t1,v1,f2,deRef(f2));
      };
      (iExists(_,_,_),_) is valof{
      	var e1 is freshenForUse(v1,D);
      	var mark is size(resets);
      	var Rslt is sub(e1,deRef(e1),t2,v2);
      	resetToMark(mark);
      	valis Rslt;
      };
      (_,iExists(_,_,_)) is valof{
      	var e2 is freshenForEvidence(v2,D);
      	var mark is size(resets);
      	var Rslt is sub(t1,v1,e2,deRef(e2));
      	resetToMark(mark);
      	valis Rslt;
      };
      (_,_) default is 
      	failed("$t1 not consistent with $t2");
    };

    subList(list of {},list of {}) is success(());
    subList(list of {A1;..T1},list of {A2;..T2}) is valof{
      var R is sub(A1,deRef(A1),A2,deRef(A2));
      if R matches success(_) then
      	valis subList(T1,T2)
      else
      	valis R
    }

    subFace(M1,T1,M2,T2) is valof{
      if size(M1)>size(M2) then
      	valis failed("$M2 has too few elements, compared to $M1")
      else{
      	for K->V1 in M1 do {
      	  if M2[K] matches V2 then {
      	    var R is sub(V1,deRef(V1),V2,deRef(V2));
      	    if not (R matches success(_)) then
      	      valis R
      	  } else
      	    valis failed("$M2 does not contain entry for $K")
      	};
      	for K->V1 in T1 do{
      	  if T2[K] matches V2 then{
      	    var R is sub(V1,deRef(V1),V2,deRef(V2));
      	    if not (R matches success(_)) then
      	      valis R
      	  } else
      	    valis failed("$T2 does not contain entry for $K")
      	}
      	valis success(());
      }
    };

    bindVar(V,T) is valof{
      if occursIn(V.name,T) then
      	valis failed("occurs check")
      else{
      	resets := list of {resetVar(V,resetLevel);..resets};
      	resetLevel := resetLevel+1;
      	V.value := T;
      	if T matches iTvar{} then
      	  valis mergeConstraints(T,V.constraints)
      	else
      	  valis checkConstraints(V.constraints,T);
      }
    };

    checkConstraints(list of {},_) is success(());
    checkConstraints(list of {C;..L},T) is 
      both((case C in {
  	    iContract(Con) is success(());
  	    iFieldCon(_,Fld,FldTp) is success(());
  	    iTypeCon(_,Fld,FldTp) is success(());
  	    hasKind(_,K) is success(());
  	    instanceOf(_,iTp) is success(());
  	    isTuple(_) is success(());
  	  }),fn ()=>checkConstraints(L,T));

    chainLength(v) is valof{
      var V := v;
      var len := 0;
      while V matches iTvar{} do {
      	len := len+1;
      	V := V.value;
      }
      valis len
    };

    both(success(_),F) is F();
    both(R,_) is R;

    checkSub(S,T) is valof{
      case sub(S,deRef(S),T,deRef(T)) in {
      	success(_) do valis success(());
      	failed(R) do {
      	  resetToMark(0);
      	  valis failed(R)
      	}
      }
    };

    resetToMark(Tgt) do {
      while list{resetVar(V,Lvl);..Rs} matches resets and Lvl>Tgt do{
      	V.value := unTyped;
      	resets := Rs;
      }
    };
  } in (S,T) => checkSub(S,T);
}