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


}