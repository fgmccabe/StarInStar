worksheet{
  import errors;
  import lexer;
  import stream;
  import operators;

  prc force(Fl) do {
    var TkSt := tokenize("file:sampletoks")

    while nextToken(TkSt,standardOps) matches (nxt,NextSt) and nxt!=terminal do {
      logMsg(info,"Token: $nxt")
      TkSt := NextSt
    }
  }

  perform force("file:sampletoks")
}