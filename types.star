types is package{

  -- kind of a type
  type kKind is kType or kUnknown or kTypeFun(integer)

  -- type structures
  type iType is iTvar{			-- type variable
    id has type integer;		-- use integers to identify vars
    name has type string;		-- original name
    value has type ref iType
    constraints has type ref list of iConstraint; -- constraints
  } or
    iKvar(integer,string) or				  -- skolem constant
    iBvar(string) or					  -- bound var
    iType(string) or					  -- simple type
    iFace(dictionary of (string,iType),dictionary of (string,iType)) or -- record type
    iTuple(list of iType) or				  -- tuple type
    iFnTp(iType,iType) or				  -- function type
    iPtTp(iType,iType) or         -- pattern type
    iConTp(iType,iType) or         -- constructor type
    iRfTp(iType) or					  -- reference type
    iTpExp(iType,iType) or			-- type application exp
    iUniv(string,iType) or			-- universally quantified type
    iExists(string,iType) or			-- existentially quantifier type
    iConstrained(iType,iConstraint) or		-- constrained type
    iContract(string,list of iType,list of iType) or -- contract type
    unTyped					-- no known type

  type iConstraint is isOver(iType) or -- contract constraint
    hasField(iType,string,iType) or -- field constraint. The first argument is the constrained type
    iFieldKind(iType,string,kKind) or -- type field kind constraint. 
    iTypeCon(iType,string,iType) or -- type field constraint. Existential constraint
    hasKind(iType,kKind) or	    -- has kind constrain
    instanceOf(iType,iType) or	    -- type instanceof constraint
    isTuple(iType);		    -- is tuple constraint

  implementation pPrint over iType is {
    fun ppDisp(T) is showType(T,2000)
  }

  fun showType(Tp matching iTvar{},Pr) is
        Tp.value = unTyped ?
          ppStr("%"++Tp.name++(Tp.id as string)) :
          showType(Tp.value,Pr)
   |  showType(iBvar(Nm),_) is ppSequence(0,[ppStr("%%"),ppStr(Nm)])
   |  showType(iType(Nm),_) is ppStr(Nm)
   |  showType(iKvar(I,N),_) is ppStr("%%"++N++(I as string))
   |  showType(iTuple(L),Pr) is showTypeList(L)
   |  showType(iFace(els,tps),_) is ppSequence(0,
          cons of [
            ppStr("{"),
            ppSequence(0,
              interleave(
                cons of {
                  all ppSequence(0,cons of [
                    ppStr(Fl),
                    ppStr(" has type "),
                    showType(Tp,1020)
                  ])
                  where Fl->Tp in els } ++
                cons of {
                  all ppSequence(0,cons of [
                    ppStr("type "),
                    ppStr(Fl),
                    ppStr(" = "),
                    showType(Tp,900)])
                  where Fl->Tp in tps}, ppStr(";"))),
            ppStr("}")])
   |  showType(iFnTp(L,R),Pr) is parenthesize(
        ppSequence(0,cons of [showType(L,904), ppStr("=>"), showType(R,905)]),
        Pr<905)
   |  showType(iPtTp(L,R),Pr) is parenthesize(
        ppSequence(0,cons of [showType(L,904), ppStr("<="), showType(R,905)]),
        Pr<905)
   |  showType(iConTp(L,R),Pr) is parenthesize(
        ppSequence(0,cons of [showType(L,904), ppStr("<=>"), showType(R,905)]),
        Pr<905)
   |  showType(iRfTp(R),Pr) is parenthesize(
        ppSequence(0,cons of [ppStr("ref "), showType(R,900)]),
        Pr<900)
   |  showType(iTpExp(L,R),Pr) is parenthesize(
        ppSequence(0,cons of [showType(L,839), ppStr(" of "), showType(R,839)]),
          Pr<840)
   |  showType(iUniv(V,R),Pr) is parenthesize(
        ppSequence(0,showUniv(iUniv(V,R),"for all ")),
          Pr<1005)
   |  showType(iExists(V,R),Pr) is parenthesize(
        ppSequence(0,showExists(iExists(V,R),"exists ")),
          Pr<1005)
   |  showType(iConstrained(T,C),Pr) is parenthesize(
        showConstrained(iConstrained(T,C)),Pr<940)
   |  showType(iContract(N,A,[]),Pr) is parenthesize(
        ppSequence(0,cons of [ppStr(N), ppSpace,ppStr("over"), ppSpace, 
          showTypeSequence(A)]),
          Pr<900)
   |  showType(iContract(N,A,D),Pr) is parenthesize(
        ppSequence(0,cons of [ppStr(N), ppSpace,ppStr("over"), ppSpace, 
          showTypeSequence(A),
          ppSpace,
          ppStr("determines"),
          ppSpace,
          showTypeSequence(D)]),
          Pr<900)
   |  showType(unTyped,_) is ppStr("<untyped>")

  private
  fun showTypeList(L) is ppSequence(0,
      cons of [
        ppStr("("),
        showTypeSequence(L),
        ppStr(")")])

  private
  fun showTypeSequence(L) is 
      ppSequence(0,
          interleave(cons of { all showType(El,999) where El in L},ppStr(", ")))

  private
  fun showUniv(iUniv(V,T),Pr) is cons of [ppStr(Pr),ppStr("%%"),ppStr(V),..showUniv(T,",")]
   |  showUniv(T,_) is cons of [ ppStr(" such that "), showType(T,1010)]

  private
  fun showExists(iExists(V,T),Pr) is cons of [ppStr(Pr),ppStr("%%"),ppStr(V),..showExists(T,",")]
   |  showExists(T,_) is cons of [ ppStr(" such that "), showType(T,1010)]

  private
  fun showConstrained(iConstrained(iConstrained(T,C),C1)) is 
        ppSequence(0,cons of [showConstrained(iConstrained(T,C)),
          ppSpace, ppStr("and"), ppSpace, showConstraint(C1)])
   |  showConstrained(iConstrained(T,C)) is 
        ppSequence(0,cons of [showType(T,939), ppSpace, ppStr("where"), ppSpace, showConstraint(C)])

  private
  fun parenthesize(E,false) is E
   |  parenthesize(E,true) is ppSequence(0,cons of [ppStr("("), E, ppStr(")")])

  private
  fun showConstraint(isOver(T)) is showType(T,999)
   |  showConstraint(hasField(T,F,FT)) is
        ppSequence(0,cons of [
          showType(T,899),
          ppSpace,
          ppStr("implements"),
          ppSpace,
          ppStr("{"),
          ppStr(F),
          ppStr(" has type "),
          showType(FT,900),
          ppStr("}")])
   |  showConstraint(iTypeCon(T,F,FT)) is
        ppSequence(0,cons of [
          showType(T,899),
          ppStr("implements"),
          ppSpace,
          ppStr("{"),
          ppStr("type "),
          ppStr(F),
          ppStr(" = "),
          showType(FT,900),
          ppStr("}")])
   |  showConstraint(hasKind(T,K)) is
        ppSequence(0,cons of [
          showType(T,899),
          ppStr(" has kind "),
          showKind(K)])
   |  showConstraint(instanceOf(L,R)) is
        ppSequence(0,cons of [
          showType(L,899),
          ppStr(" instance of "),
          showType(R,899)])
   |  showConstraint(isTuple(T)) is
        ppSequence(0,cons of [ showType(T,899), ppStr(" is tuple")])

  private
  fun showKind(kType) is ppStr("type")
   |  showKind(kUnknown) is ppStr("unknown")
   |  showKind(kTypeFun(0)) is ppStr("type")
   |  showKind(kTypeFun(1)) is ppStr("type of type")
   |  showKind(kTypeFun(A)) is ppSequence(0, cons of [
        ppStr("type of ("),
        ppSequence(0,interleave(
          cons of {all ppStr("type") where ix in range(0,A,1)},
          ppStr(","))),
        ppStr(")")
      ])
      
  fun varsInType(T) is let{
    fun varsIn(soFar,Tp matching iTvar{}) is checkVar(soFar,deRef(Tp))
     |  varsIn(soFar,iFace(Vals,Types)) is 
          mapFold(varsIn,mapFold(varsIn,soFar,Vals),Types)
     |  varsIn(soFar,iTuple(L)) is leftFold(varsIn,soFar,L)
     |  varsIn(soFar,iFnTp(L,R)) is varsIn(varsIn(soFar,L),R)
     |  varsIn(soFar,iPtTp(L,R)) is varsIn(varsIn(soFar,L),R)
     |  varsIn(soFar,iRfTp(R)) is varsIn(soFar,R)
     |  varsIn(soFar,iTpExp(L,R)) is varsIn(varsIn(soFar,L),R)
     |  varsIn(soFar,iUniv(N,BTp)) is varsIn(soFar,BTp)
     |  varsIn(soFar,iExists(N,BTp)) is varsIn(soFar,BTp)
     |  varsIn(soFar,iConstrained(CTp,Cn)) is inCon(varsIn(soFar,CTp),Cn)
     |  varsIn(soFar,iContract(_,At,Dt)) is leftFold(varsIn,leftFold(varsIn,soFar,At),Dt)
     |  varsIn(soFar,_) default is soFar

    fun inCon(soFar,isOver(Ct)) is varsIn(soFar,Ct)
     |  inCon(soFar,hasField(_,_,BTp)) is varsIn(soFar,BTp)
     |  inCon(soFar,iTypeCon(_,_,BTp)) is varsIn(soFar,BTp)
     |  inCon(soFar,instanceOf(L,R)) is varsIn(varsIn(soFar,L),R)
     |  inCon(soFar,hasKind(L,_)) is varsIn(soFar,L)
     |  inCon(soFar,isTuple(L)) is varsIn(soFar,L)

    fun checkVar(soFar,iTvar{id=N}) is add_element(soFar,N)
     |  checkVar(soFar,Tp) is varsIn(soFar,Tp)
  } in varsIn(set of [],T)

  private
  mapFold has type ((set of integer,iType)=>set of integer,set of integer,dictionary of (string,iType))=>set of integer
  fun mapFold(F,I,D) is leftFold((A,(_,T))=>F(A,T),I,D)

  fun occursIn(Id,T) is contains_element(varsInType(T),Id)

  fun deRef(tV matching iTvar{}) is tV.value=unTyped ? tV : deRef(tV.value)
   |  deRef(T) default is T

  fun typeName(Tp) is switch deRef(Tp) in {
    case iType(Nm) is some(Nm)
    case iTpExp(Op,Nm) is typeName(Op)
    case iTuple(L) is some("()$(size(L))")
    case iContract(_,_,_) is implName(deRef(Tp))
    case iUniv(_,QT) is typeName(QT)
    case iExists(_,QT) is typeName(QT)
    case iConstrained(CT,_) is typeName(CT)
    case _ default is none
  }

  fun implName(iContract(Nm,At,_)) is let {
        fun addInTp(some(SoF),Tp) is typeName(Tp) has value TNm ? some(SoF++"#"++TNm) : none
         |  addInTp(St,_) default is St
      } in leftFold(addInTp,some("$"++Nm),At)
   |  implName(iUniv(_,Tp)) is implName(Tp)
}
