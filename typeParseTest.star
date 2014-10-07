worksheet{
  import errors;
  import lexer;
  import stdNames;
  import operators;
  import ast;
  import opgrammar;
  import parseType;

	-- test the type parser

  loadUri has type (uri)=>string;
  loadUri(U) is string(__getUri(U));

  parseString(Text) is valof{
    Toks is tokenize(Text,noUri,(0,1,0));

    (Rest,Pr,T) is term(Toks,2000,standardOps);

    valis T
  }

  var P is parseString("for all e,f such that (c of e,(e)=>f) => c of f")

  show parseType(P,dictionary of {})
}