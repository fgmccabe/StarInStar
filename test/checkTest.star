worksheet{
	import parseForTest
	import parseType
	import freshen
	import check
  import canonical
  import types
  import good

	/*
	def factTerm is parseFile("file:fact.star")

	show factTerm

	def factType is pkgType(factTerm,stdDict)

	show factType
	*/


  -- type check function application

  def pT is parseType(parseString("(integer,integer)=>integer"),stdDict)

  var D := declareVar(stdDict,"plus",varEntry{tipe=pT})
  D := declareVar(D,"minus",varEntry{tipe=pT})
  D := declareVar(D,"times",varEntry{tipe=pT})

  def e is parseString("plus(times(2,3),4)")

  show typeOfExp(e,typeVar(),D,D)

  -- A type error ...

  def b is "plus(times(2,3),4.5)"

  show typeOfExp(parseString(b),typeVar(),D,D)

  -- factorial
  def f is parseString("let { fun fact(0) is 1 | fact(N) is times(N,fact(minus(N,1))) } in fact")

  show f

  show typeOfExp(f,typeVar(),D,D)
}