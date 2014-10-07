dict is package{
  -- the dictionary contains descriptions of variables, types etc.
  private import canonical;

  type typeEntry is typeExists(string,kKind) or
    algebraic() or
    typeAlias(string,kKind,(iType)=>maybe of iType); -- the alias is actually in the form of a function

  type varEntry is varEntry{
    name has type string;
    tipe has type iType;
  }

  type dict is dict{
    names has type dictionary of (string, varEntry)
    types has type dictionary of (string, typeEntry)
    outer has type dict;
  }
  
  findType(dict{types=Tp},Nm) is _index(Tp,Nm);
    
}