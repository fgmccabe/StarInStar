testPairHeap is package{
  import pairHeap;

  def orderedStrings is ordered{
    type string counts as t;

    fun leq(x,y) is x<=y;
    fun eq(x,y) is x=x;
    fun gt(x,y) is x>y;
  }

  def stringHeap is pairHeap(orderedStrings);

  prc main() do {
    def e is stringHeap.empty;

    assert stringHeap.isEmpty(e);

    def f1 is stringHeap.insrt("beta" cast orderedStrings.t,e);

    def f2 is stringHeap.insrt("alpha" cast orderedStrings.t,f1);

    def f3 is stringHeap.insrt("gamma" cast orderedStrings.t,f2);
  }
}
