worksheet{
  import errors;
  import lexer;
  import operators;
  import stream;
  import opgrammar;
  import ast

  var tokens is tokenize("file:sampleTerm")

  show term(tokens,2000,standardOps)
}