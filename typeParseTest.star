worksheet{
  import errors;
  import lexer;
  import operators;
  import stream;
  import opgrammar;
  import ast
  import types;
  import parseType;
  import dict;

	-- test the type parser


  parseString(Text) is valof{
    var tokens is tokenize("file:sampleTypes")
    var (Rest,Pr,T) is term(tokens,2000,standardOps);

    valis T
  }

  var P is parseString("for all e,f such that (c of e,(e)=>f) => c of f")

  show "parse ($P) for types"

  var D := dict{ names = dictionary of []; types = dictionary of ["c"->typeIs(iUniv("t",iTpExp(iType("c"),iBvar("t"))))]; outer = none}

  show parseType(P,D)
}