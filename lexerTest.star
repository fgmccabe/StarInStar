worksheet{
  import errors;
  import lexer;
  import operators;
  import stream;

  force(Fl) do {
    var TkSt := tokenize("file:sampletoks")

    while nextToken(TkSt,standardOps) matches (nxt,NextSt) and nxt!=terminal do {
      logMsg(info,"Token: $nxt")
      TkSt := NextSt
    }
  }

  perform force("file:sampletoks")
}