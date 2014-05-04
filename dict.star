dict is package{
  -- the dictionary contains descriptions of variables, types etc.
  private import canonical;

  type typeEntry is typeExists(string,kKind) or
    algebraic() or
    typeAlias(string,kKind,(iType)=>maybe of iType); -- the alias is actually in the form of a function

  type dictionary is dict{
    types has type map of (string,typeEntry)
    outer has type dictionary;
  }
  
  findType(dict{types=Tp},Nm) is _index(Tp,Nm);
    
}