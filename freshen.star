freshen is package{
  private import types
  -- private import dict

  private 
  fun frshn(iExists(bV,bT),M,U,E) is frshn(bT,E(bV,M),U,E)
   |  frshn(iUniv(bV,bT),M,U,E) is frshn(bT,U(bV,M),U,E)
   |  frshn(Typ,M,_,_) is let{
        fun frshnUp(Mp) is let{
          fun rewrite(Tp) is switch Tp in {
            case iTvar{value=V} is V=unTyped?Tp:rewrite(V)
          	case iKvar(_,_) is Tp
          	case iBvar(Nm) where Mp[Nm] has value Kt is Kt
          	case iType(_) is Tp
          	case iFace(Flds,Tps) is iFace(frMap(Flds),frMap(Tps))
          	case iTuple(Flds) is iTuple(map(rewrite,Flds))
            case iFnTp(A,R) is iFnTp(rewrite(A),rewrite(R))
            case iConTp(A,R) is iConTp(rewrite(A),rewrite(R))
          	case iPtTp(A,R) is iPtTp(rewrite(A),rewrite(R))
          	case iRfTp(T) is iRfTp(rewrite(T))
          	case iTpExp(T,A) is iTpExp(rewrite(T),rewrite(A))
          	case iUniv(Nm,bTp) is let{
          	       def xF is frshnUp(Mp[without Nm])
          	     } in iUniv(Nm,xF(bTp))
          	case iExists(Nm,bTp) is let{
          	       def xF is frshnUp(Mp[without Nm])
          	     } in iExists(Nm,xF(bTp))
          	case iConstrained(A,X) is valof{
                frCon(X)
                valis rewrite(A)
          	  }
          	case unTyped is unTyped
          }

          prc frCon(iContractCon(iContract{name=Cx; argTypes=Ax; depTypes=Dx})) do {
              	def nAx is map(rewrite,Ax)
              	def nI is iContractCon(iContract{name=Cx;argTypes=nAx;depTypes=map(rewrite,Dx)})
              	for A in nAx do
              	  setConstraint(A,nI)
              }
           |  frCon(iFieldCon(rTp,Nm,fTp)) do {
              	def nAx is rewrite(rTp)
              	setConstraint(nAx,iFieldCon(nAx,Nm,rewrite(fTp)))
              }
           |  frCon(iTypeCon(rTp,Nm,fTp)) do {
              	def nAx is rewrite(rTp)
              	setConstraint(nAx,iTypeCon(nAx,Nm,rewrite(fTp)))
              }
           |  frCon(hasKind(rTp,K)) do {
              	def nAx is rewrite(rTp)
              	setConstraint(nAx,hasKind(nAx,K))
              }
           |  frCon(instanceOf(rTp,fTp)) do{
              	def nTp is rewrite(rTp)
              	def xTp is rewrite(fTp)
              	def nI is instanceOf(nTp,xTp)
              	setConstraint(nTp,nI)
              	setConstraint(xTp,nI)
              }
           |  frCon(isTuple(rTp)) do {
              	def nTp is rewrite(rTp)
              	setConstraint(nTp,isTuple(nTp))
              }

          frMap has type (dictionary of (string,iType))=>dictionary of (string,iType)
          fun frMap(Flds) is dictionary of {all (K,rewrite(V)) where K->V in Flds}

          fun rewriteKinds(Kds) is dictionary of {all (T,someValue(Mp[T])) where T->_ in Kds}

          fun kindConstrain(T,KM) is _checkIterState(
          	_ixiterate(KM,
               (FT,FK,ContinueWith(Tp))=>ContinueWith(
          	    iConstrained(Tp,hasKind(someValue(Mp[FT]),FK))),
        	    ContinueWith(T)),razer)
          fun razer() is raise "problem"
        } in rewrite
  } in frshnUp(M)(Typ)

  private
  prc setConstraint(T matching iTvar{ constraints := Cs },Cx) do 
        T.constraints := list of [Cx,..Cs]
   |  setConstraint(_,_) do nothing
  
  private 
  var counter := 0
  private
  fun nextId() is valof{
    counter := counter+1
    valis counter
  }

  private
  fun nVar(Nm,Mp) is Mp[with Nm -> iTvar{
      id = nextId()
      name = Nm
      value := unTyped
      constraints := []
    }]

  private
  fun skolemize(Nm,Mp) is
    valof{
      def UVars is list of { all V where (V matching iTvar{}) in Mp }
      if isEmpty(UVars) then
      	valis Mp[with Nm->iKvar(nextId(),Nm)]
      else
      	valis Mp[with Nm->iTpExp(iKvar(nextId(),Nm),iTuple(UVars))]
    }

  fun freshenForUse(Tp) is frshn(Tp,dictionary of [],nVar,skolemize)
  fun freshenForEvidence(Tp) is frshn(Tp,dictionary of [],skolemize,nVar)

  fun typeVar() is iTvar{ id = nextId(); name="t$id"; value := unTyped; constraints := []}
}