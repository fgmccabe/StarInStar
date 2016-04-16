worksheet{
  import errors;
  import lexer;
  import operators;
  import stream;
  import opgrammar;
  import ast

  fun parse(Fn) is valof{
    def tokens is tokenize(Fn)
    valis term(tokens,2000,standardOps)
  }

  prc force(Fl) do {    
    logMsg(info,"tokens from $Fl")

    var TkSt := tokenize(Fl)

    while nextToken(TkSt,standardOps) matches (nxt,NextSt) and nxt!=terminal do {
      logMsg(info,"Token: $nxt")
      TkSt := NextSt
    }
  }

  show parse("file:sampleTerm")

  show parse("file:testInnerOper")

  show parse("file:arithTest.star")
}