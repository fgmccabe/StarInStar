genes is package{
  -- implement a simple genetics structure

  fun mergeGene(G1,G2) is map of {
    all (G,V) where G->V1 in G1 and G->V2 in G2 and (random(1.0)>0.5 ? V bound to V1 | V bound to V2 )}

  fun mutate(G,Epsilon) is map of { all (K,V1+(random(1.0)-0.5)*Epsilon/V1) where K->V1 in G }

  prc main() do {
    def G1 is map of {"alpha"->0.2; "beta"->0.3; "gamma"->0.75};
    def G2 is map of {"alpha"->0.8; "beta"->0.65; "gamma"->0.5};

    logMsg(info,"G1m is $(mutate(G1,0.01))");
    logMsg(info,"G2m is $(mutate(G2,0.01))");

    logMsg(info,"M1 is $(mergeGene(G1,G2))");
  }
}