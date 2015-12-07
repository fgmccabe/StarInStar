typeUtils is package{
  private import types;
  private import freshen

  fun optionType(Tp) is iTpExp(iType("option"),Tp)

  fun contractConstrainedType(Co,Det) is valof{
    def Tp is typeVar()
    def con is iContract{name=Co;argTypes=[Tp];depTypes=Det}
    
    Tp.constraints := [iContractCon(con)]

    valis Tp
  }

  fun funType(argTypes,resType) is iFnTp(iTuple(argTypes),resType)
  
/*
  fun sealType(Tp,D) is switch deRef(Tp) in {
    case iTvar{} is iFace(dictionary of [],dictionary of [])

    iKvar(integer,string) or          -- skolem constant
    iBvar(string) or            -- bound var
    iType(string) or            -- simple type
    iFace(dictionary of (string,iType),dictionary of (string,iType)) or -- record type
    iTuple(list of iType) or          -- tuple type
    iFnTp(iType,iType) or         -- function type
    iPtTp(iType,iType) or         -- pattern type
    iConTp(iType,iType) or         -- constructor type
    iRfTp(iType) or           -- reference type
    iTpExp(iType,iType) or      -- type application exp
    iUniv(string,iType) or      -- universally quantified type
    iExists(string,iType) or      -- existentially quantifier type
    iConstrained(iType,iConstraint) or    -- constrained type
    unTyped;          -- no known type
  }
  */
}