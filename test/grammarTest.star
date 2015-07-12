worksheet{
  import errors;
  import lexer;
  import operators;
  import stream;
  import opgrammar;
  import ast

  def tokens is tokenize("file:sampleTerm")

  show term(tokens,2000,standardOps)

  show term(tokenize("file:testInnerOper"),2000,standardOps)
}