freshen is package{
  private import types

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
            case iContract(Nm,At,Dt) is iContract(Nm,map(rewrite,At),map(rewrite,Dt))
          	case iConstrained(A,X) is valof{
                frCon(X)
                valis rewrite(A)
          	  }
          	case unTyped is unTyped
          }

          prc frCon(isOver(iContract(Cx,Ax,Dx))) do {
              	def nAx is map(rewrite,Ax)
              	def nI is isOver(iContract(Cx,nAx,map(rewrite,Dx)))
              	for A in nAx do
              	  setConstraint(A,nI)
              }
           |  frCon(hasField(rTp,Nm,fTp)) do {
              	def nAx is rewrite(rTp)
              	setConstraint(nAx,hasField(nAx,Nm,rewrite(fTp)))
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
  } in (frshnUp(M)(Typ),M)

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

  fun freshen(Tp) where freshenForUse(Tp) matches (fTp,_) is fTp
  fun evidence(Tp) where freshenForEvidence(Tp) matches (fTp,_) is fTp

  fun stripQuants(iExists(bV,bT),M,U,E) is stripQuants(bT,E(bV,M),U,E)
   |  stripQuants(iUniv(bV,bT),M,U,E) is stripQuants(bT,U(bV,M),U,E)
   |  stripQuants(T,M,_,E) is (T,M)

  fun typeVar() is valof{
    def I is nextId();
    valis iTvar{ id = I; name="t$I"; value := unTyped; constraints := []}
  }

  fun generalize(tipe,Occurs) is let {
    var foundVars := dictionary of []
    var constraints := set of []
    fun genType(Tp) is switch deRef(Tp) in {
      case iTvar{} is genVar(deRef(Tp))
      case iKvar(_,_) is Tp
      case iBvar(Nm) is Tp
      case iType(_) is Tp
      case iFace(Flds,Tps) is iFace(frMap(Flds),frMap(Tps))
      case iTuple(Flds) is iTuple(map(genType,Flds))
      case iFnTp(A,R) is iFnTp(genType(A),genType(R))
      case iConTp(A,R) is iConTp(genType(A),genType(R))
      case iPtTp(A,R) is iPtTp(genType(A),genType(R))
      case iRfTp(T) is iRfTp(genType(T))
      case iTpExp(T,A) is iTpExp(genType(T),genType(A))
      case iUniv(Nm,bTp) is iUniv(Nm,genType(bTp))
      case iExists(Nm,bTp) is iExists(Nm,genType(bTp))
      case iConstrained(A,X) is iConstrained(genType(A),genConstraint(X))
      case iContract(Nm,A,D) is iContract(Nm,map(genType,A),map(genType,D))
      case unTyped is unTyped
    }

    fun frMap(Flds) is dictionary of {all Nm->genType(Tp) where Nm->Tp in Flds}

    fun genVar(Tp matching iTvar{id=i;name=name;constraints=c}) is 
      foundVars[Tp] has value gTp ? gTp : Occurs(Tp) ? Tp : valof{
        def boundVar is iBvar(name)
        foundVars[Tp] := boundVar
        for con in c do {
          extend constraints with con
        }
        valis boundVar
      }

    fun genConstraint(isOver(iContract(conName,argTypes,depTypes))) is
          isOver(iContract(conName,map(genType,argTypes),map(genType,depTypes)))
     |  genConstraint(hasField(Tp,Name,fldTp)) is hasField(genType(Tp),Name,genType(fldTp))
     |  genConstraint(iFieldKind(Tp,N,K)) is iFieldKind(genType(Tp),N,K)
     |  genConstraint(iTypeCon(Tp,N,fldTp)) is iTypeCon(genType(Tp),N,genType(fldTp))
     |  genConstraint(hasKind(Tp,K)) is hasKind(genType(Tp),K)
     |  genConstraint(instanceOf(Tp,iTp)) is instanceOf(genType(Tp),genType(iTp))
     |  genConstraint(isTuple(Tp)) is isTuple(genType(Tp))

    fun bindTp((_,iBvar(nm)),tp) is iUniv(nm,tp)

    fun bindCon(Cn,T) is iConstrained(T,genConstraint(Cn))

  } in valof{
      def gTp is genType(tipe)
      valis rightFold(bindTp,rightFold(bindCon,gTp,constraints),foundVars)
    }
}