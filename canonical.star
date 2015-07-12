canonical is package{
  private import location
  import types

  -- define the typed term structure. This is the main workhorse structure for representing Star programs


  -- define the canonical structures themselves
  type canon is expr{
    tipe has type iType
    loc has type srcLoc
    exp has type cExp
  }
  or pttrn{
    tipe has type iType
    loc has type srcLoc
    pttrn has type cPtn
  } or cond {
    loc has type srcLoc
    cond has type cCond
  }

  type cExp is 
       cVar(string)   -- a variable of some form
    or cDeRef(canon)  -- dereference a variable
    or cInt(integer)
    or cLong(long)
    or cFloat(float)
    or cDecimal(decimal)
    or cChar(char)
    or cString(string)
    or cTuple(list of canon)
    or cFace(dictionary of (string,canon),dictionary of (string,iType))
    or cField(canon,string)
    or cApply(canon,canon)
    or cLambda(canon,canon)
    or cMemo(canon)

  type cPtn is 
       pVar(string) -- a new variable
    or pInt(integer)
    or pLong(long)
    or pFloat(float)
    or pDecimal(decimal)
    or pChar(char)
    or pString(string)
    or pTuple(list of canon)
    or pFace(dictionary of (string,canon),dictionary of (string,iType))
    or pWhere(canon,canon)
    or pApply(canon,canon)

  type cCond is 
       cAnd(canon,canon)
    or cOr(canon,canon)
    or cNot(canon)
    or cImplies(canon,canon)
    or cOtherwise(canon,canon)
    or cCond(canon,canon,canon)
    or cSearch(canon,canon)
    or cIxSearch(canon,canon,canon)
    or cExp(canon)
}