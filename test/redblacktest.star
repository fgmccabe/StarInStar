redblacktest is package{
  import redblack;

  prc main() do {
    def SS is redblack of ["alpha"->1, "gamma"->2, "beta"->3, "delta"->4, "omega"->5, "iota"->6];
    def TT is redblack of ["eta"->7, "omega"->8];

    logMsg(info,"SS=$SS");

    for K->V in SS do
      logMsg(info,"K=$K,V=$V");

    assert SS["alpha"] has value 1;

    assert _index(SS,"aleph")=none;

    def XX is redblack of [0cS->0, 0cE->1, 0cA->2, 0cR->3, 0cC->4, 0cH->5, 0cX->6, 0cM->7, 0cP->8, 0cL->9 ];
    logMsg(info,__display(XX));
  }
}
