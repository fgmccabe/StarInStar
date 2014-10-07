freshen is package{
  private import types;
  private import dict;

  private 
  frshn(iExists(bV,bT),M,U,E) is frshn(bT,E(bV,M),U,E);
  frshn(iUniv(bV,bT),M,U,E) is frshn(bT,U(bV,M),U,E);
  frshn(Typ,M,_,_) is let{
    frshnUp(Mp) is let{
      rewrite(Tp) is case Tp in {
        iTvar{value=V} is V=unTyped?Tp|rewrite(V);
      	iKvar(_,_) is Tp;
      	iBvar(Nm) is Mp[Nm];
      	iType(_) is Tp;
      	iFace(Flds,Tps) is iFace(frMap(Flds),frMap(Tps));
      	iTuple(Flds) is iTuple(map(Flds,rewrite));
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
      	iConstrained(A,X) is valof{
          frCon(X);
          valis rewrite(A)
      	}
      	unTyped is unTyped;
      };

      frCon(iContract(Cx,Ax,Dx)) do {
      	var nAx is map(Ax,rewrite);
      	var nI is iContract(Cx,nAx,map(Dx,rewrite));
      	for A in nAx do
      	  setConstraint(A,nI)
      };
      frCon(iFieldCon(rTp,Nm,fTp)) do{
      	var nAx is rewrite(rTp);
      	setConstraint(nAx,iFieldCon(nAx,Nm,rewrite(fTp)))
      }
      frCon(iTypeCon(rTp,Nm,fTp)) do {
      	var nAx is rewrite(rTp);
      	setConstraint(nAx,iTypeCon(nAx,Nm,rewrite(fTp)));
      }
      frCon(hasKind(rTp,K)) do {
      	var nAx is rewrite(rTp);
      	setConstraint(nAx,hasKind(nAx,K));
      }
      frCon(instanceOf(rTp,fTp)) do{
      	var nTp is rewrite(rTp);
      	var xTp is rewrite(fTp);
      	var nI is instanceOf(nTp,xTp);
      	setConstraint(nTp,nI);
      	setConstraint(xTp,nI);
      }
      frCon(isTuple(rTp)) do {
      	var nTp is rewrite(rTp);
      	setConstraint(nTp,isTuple(nTp));
      }

      frMap has type (dictionary of (string,iType))=>dictionary of (string,iType);
      frMap(Flds) is dictionary of {all (K,rewrite(V)) where K->V in Flds};

      rewriteKinds(Kds) is dictionary of {all (T,Mp[T]) where T->_ in Kds};

      kindConstrain(T,KM) is _checkIterState(
      	_ixiterate(KM,
          fn (FT,FK,ContinueWith(Tp))=>ContinueWith(
      	    iConstrained(Tp,hasKind(Mp[FT],FK))),
    	    ContinueWith(T)),razer)
      razer() is raise "problem";
    } in rewrite;
  } in frshnUp(M)(Typ);

  private
  setConstraint(T matching iTvar{ con := Cs },Cx) do 
    T.con := list of [Cx,..Cs];
  setConstraint(_,_) do nothing;
  
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
      con := [];
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

  freshenForUse(Tp) is frshn(Tp,dictionary of {},nVar,skolemize);
  freshenForEvidence(Tp) is frshn(Tp,dictionary of {},skolemize,nVar);
}