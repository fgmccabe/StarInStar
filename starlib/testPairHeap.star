testPairHeap is package{
  import pairHeap;

  orderedStrings is ordered{
    type string counts as t;

    leq(x,y) is x<=y;
    eq(x,y) is x=x;
    gt(x,y) is x>y;
  }

  stringHeap is pairHeap(orderedStrings);

  main() do {
    e is stringHeap.empty;

    assert stringHeap.isEmpty(e);

    f1 is stringHeap.insrt("beta" cast orderedStrings.t,e);

    f2 is stringHeap.insrt("alpha" cast orderedStrings.t,f1);

    f3 is stringHeap.insrt("gamma" cast orderedStrings.t,f2);
  }
}
