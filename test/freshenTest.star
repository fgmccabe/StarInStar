worksheet{
  import freshen;
  import types;

  show iFnTp(iTuple(list of [iType("string"), iType("integer")]),
      iType("float"))

  assert display(iFnTp(iTuple(list of [iType("string"), iType("integer")]),
      iType("float"))) = "(string, integer)=>float"

  def idType is iUniv("t",iFnTp(iTuple(list of [iBvar("t")]), iBvar("t")))

  show idType;

  show freshenForUse(idType);

  show freshenForEvidence(idType);

  def lType is iTpExp(iType("list"),iType("string"))

  show lType;

  -- map type
  def mpType is iUniv("s",iUniv("t",
    	iFnTp(iTuple(list of [
    	    iFnTp(iTuple(list of [iBvar("s")]),iBvar("t")),
    	    iTpExp(iType("list"),iBvar("s"))]),
    	  iTpExp(iType("list"),iBvar("t")))));

  show mpType;
  show freshenForUse(mpType);
  show freshenForEvidence(mpType);

  -- record types
  def rcType is iUniv("s",iExists("t",
    iConstrained(
      iFace(
        dictionary of [
          "name" -> iType("string"),
          "id" -> iBvar("t"),
          "mp" -> iFnTp(iTuple(list of [iBvar("s")]),iBvar("t"))
        ],
        dictionary of [
        "t" -> iBvar("t")
        ]
      ),
      hasKind(iBvar("t"),kType))))

  show rcType;
  show freshenForUse(rcType);
  show freshenForEvidence(rcType);
}

  