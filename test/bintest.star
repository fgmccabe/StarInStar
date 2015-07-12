bintest is package{
  import binomial;

  prc main() do {
    def SS is binomial of ["alpha", "gamma", "beta", "delta", "omega", "iota"];
    def TT is binomial of ["eta", "omega"];

    logMsg(info,"SS=$SS");
    logMsg(info,"SS++TT=$(SS++TT)");

    assert SS++TT=TT++SS;

    var S := SS;

    update (X where X>"beta") in S with "_"++X;

    logMsg(info,"S is now $S");
  }
}