worksheet{
  import parseForTest
  import parseType
  import freshen
  import dict
  import check
  import canonical
  import types
  import good

  -- type check id function

  def pT is parseType(parseString("(integer,integer)=>integer"),stdDict)

  var D := declareVar(stdDict,"plus",varEntry{tipe=pT})
  D := declareVar(D,"minus",varEntry{tipe=pT})
  D := declareVar(D,"times",varEntry{tipe=pT})

  -- id
  def f is parseString("let { fun id(X) is X } in id")

  show f

  show typeOfExp(f,typeVar(),D,D)

  show typeOfExp(parseString("let { fun id(X) is X; def a is id(23); def b is id(\"fred\") } in id(b)"),typeVar(),D,D)
}