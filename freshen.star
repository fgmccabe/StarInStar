freshen is package{
  private import types;
  private import dict;

  private 
  frshn(iExists(bV,bT),M,U,E) is frshn(bT,E(bV,M),U,E);
  frshn(iUniv(bV,bT),M,U,E) is frshn(bT,U(bV,M),U,E);
  frshn(Typ,M,_,_) is let{
    frshnUp(Mp) is let{
      rewrite(Tp) is case deRef(Tp) in {
	iTvar{} is Tp;
	iKvar(_,_) is Tp;
	iBvar(Nm) is Mp[Nm];
	iType(_) is Tp;
	iFace(Flds,Tps) is iFace(rewriteMap(Flds),rewriteMap(Tps));
	iRecord(Flds,Kds) is kindConstrain(
	  iFace(rewriteMap(Flds),rewriteKinds(Kds)),Kds);
	iTuple(Flds) is iTuple(_map(Flds,rewrite));
	iFnTp(A,R) is iFnTp(rewrite(A),rewrite(R));
	iPtTp(A,R) is iPtTp(rewrite(A),rewrite(R));
	iRfTp(T) is iRfTp(rewrite(T));
	iTpExp(T,A) is iTpExp(rewrite(T),rewrite(A));
	iUniv(Nm,bTp) is let{
	  var xF is frshnUp(Mp[without Nm]);
	} in iUniv(Nm,xF(bTp));
	iExists(Nm,bTp) is let{
	  var xF is frshnUp(Mp[without Nm]);
	} in iExists(Nm,xF(bTp));
	iConstrained(A,X) is iConstrained(rewrite(A),frshnCon(X));
	unTyped is unTyped;
      };

      frshnCon(iContract(CTp)) is iContract(rewrite(CTp));
      frshnCon(iFieldCon(rTp,Nm,fTp)) is iFieldCon(rewrite(rTp),Nm,rewrite(fTp));
      frshnCon(iTypeCon(rTp,Nm,fTp)) is iTypeCon(rewrite(rTp),Nm,rewrite(fTp));
      frshnCon(hasKind(rTp,K)) is hasKind(rewrite(rTp),K);
      frshnCon(instanceOf(rTp,fTp)) is instanceOf(rewrite(rTp),rewrite(fTp));
      frshnCon(isTuple(rTp)) is isTuple(rewrite(rTp));

      rewriteMap has type (map of (string,iType))=>map of (string,iType);
      rewriteMap(Flds) is map of {all (K,rewrite(V)) where K->V in Flds};

      rewriteKinds(Kds) is map of {all (T,Mp[T]) where T->_ in Kds};

      kindConstrain(T,KM) is _checkIterState(
	_ixiterate(KM,
	    fn (FT,FK,ContinueWith(Tp))=>ContinueWith(
	    iConstrained(Tp,hasKind(Mp[FT],FK))),
	    ContinueWith(T)),razer)
      razer() is raise "problem";
    } in rewrite;
  } in frshnUp(M)(Typ);

  private 
  var counter := 0;
  private nextId() is valof{
    counter := counter+1;
    valis counter;
  }

  private
  nVar(Nm,Mp) is Mp[with Nm -> iTvar{
      id = nextId();
      name = Nm;
      value := unTyped;
    }];

  private
  skolemize(Nm,Mp) is
    valof{
      UVars is list of { all V where (V matching iTvar{}) in Mp }
      if isEmpty(UVars) then
	valis Mp[with Nm->iKvar(nextId(),Nm)]
      else
	valis Mp[with Nm->iTpExp(iKvar(nextId(),Nm),
	    iTuple(UVars))]
    }

  freshenForUse(Tp) is frshn(Tp,map of {},nVar,skolemize);
  freshenForEvidence(Tp) is frshn(Tp,map of {},skolemize,nVar);
}