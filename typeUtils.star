typeUtils is package{
  private import types;
  private import freshen

  fun optionType(Tp) is iTpExp(iType("option"),Tp)

  fun contractConstrainedType(Co,Det) is valof{
    def Tp is typeVar()
    def con is iContract(Co,[Tp],Det)
    
    Tp.constraints := [isOver(con)]

    valis Tp
  }

  fun funType(argTypes,resType) is iFnTp(iTuple(argTypes),resType)
}