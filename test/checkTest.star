worksheet{
	import parseForTest
	import parseType
	import freshen
	import dict
	import check

	/*
	def factTerm is parseFile("file:fact.star")

	show factTerm

	def factType is pkgType(factTerm,stdDict)

	show factType
	*/


  -- type check function application

  def pT is parseType(parseString("(integer,integer)=>integer"),stdDict)

  var D := declareVar(stdDict,"plus",varEntry{tipe=pT})

  D := declareVar(D,"times",varEntry{tipe=pT})

  def e is parseString("plus(times(2,3),4)")


  show typeOfExp(e,typeVar(),D,D)
}