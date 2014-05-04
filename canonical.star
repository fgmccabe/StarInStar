canonical is package{
  private import location;
  import types;

  -- define the typed term structure. This is the main workhorse structure for representing Star programs


  -- define the canonical structures themselves
/*
  type canon is cVoid(srcLoc,iType) or  -- illegal entity
    cVar(srcLoc,string,iType) or	-- a variable of some form
    
*/
/*  implementation coercion over (iType,quoted) is {
    coerce(T) is first(convert(deRef(T),map of {}));
  } using {
    convert(iKVar(Nm),M) is (nameAst(noWhere,Nm),M);
    convert(iType(Nm,_),M) is (nameAst(noWhere,Nm),M);
    convert(iTpExp(Con,Args),M) is valof{
      (H,M1) is convert(Con,M);
      (A,M2) is convertArgs(Args,M1)
      valis  <| ?H of 
*/
}