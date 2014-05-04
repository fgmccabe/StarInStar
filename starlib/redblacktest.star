redblacktest is package{
  import redblack;

  main() do {
    SS is redblack of {"alpha"->1; "gamma"->2; "beta"->3; "delta"->4; "omega"->5; "iota"->6};
    TT is redblack of {"eta"->7; "omega"->8};

    logMsg(info,"SS=$SS");

    for K->V in SS do
      logMsg(info,"K=$K,V=$V");

    assert SS["alpha"] = 1;

    assert _index(SS,"aleph")=none;

    XX is redblack of {'S'->0; 'E'->1; 'A'->2; 'R'->3; 'C'->4; 'H'->5; 'X'->6; 'M'->7; 'P'->8; 'L'->9 };
    logMsg(info,__display(XX));
  }
}
