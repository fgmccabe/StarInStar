worksheet{
  import parseForTest
  import parseType
  import freshen
  import check
  import canonical
  import types
  import good
  import stdTypes

  -- type check id function

  def good(pT) is parseType(parseString("(integer,integer)=>integer"),stdDict)

  var D := declareVar(stdDict,"plus",varEntry{proto=cVar{loc=missing;name="plus";tipe=pT}})
  D := declareVar(D,"minus",varEntry{proto=cVar{loc=missing;name="minus";tipe=pT}})
  D := declareVar(D,"times",varEntry{proto=cVar{loc=missing;name="times";tipe=pT}})

  -- id
  def f is parseString("let { fun id(X) is X } in id")

  show f

  show typeOfExp(f,typeVar(),D,D)

  def i is typeOfExp(parseString("let { id has type for all t such that (t)=>t; fun id(X) is X; def a is id(23); def b is id(\"fred\") } in id(b)"),typeVar(),D,D)

  show i
  assert more(i,(x)=>good(x.tipe=iType("string"))) = good(true)
}