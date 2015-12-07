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
  import freshen;
  import parseForTest

	-- test the type parser

  def P is parseString("for all e,f such that (c of e,(e)=>f) => c of f")

  show "parse ($P) for types"

  var D := declareType(stdDict,"c",typeIs(iUniv("t",iTpExp(iType("c"),iBvar("t")))))

  show parseType(P,D)

  def P2 is parseString("for all r,n such that (r)<=>n where r implements { name has type n}")

  show "parse [$P2]"

  show parseType(P2,D)

  show freshenForUse(parseType(P2,D))

  D := declareAlgebraic(D,"option",iUniv("t",iTpExp(iType("option"),iBvar("t"))), 
      dictionary of ["none"->iUniv("t",iTpExp(iType("option"),iBvar("t"))),
                     "some"->iUniv("t",iConTp(iBvar("t"),iTpExp(iType("option"),iBvar("t"))))])

  def P3 is parseString("for all r,n such that (r)=>option of n where sequence over r determines n")

  show __display(parseType(P3,D))
}