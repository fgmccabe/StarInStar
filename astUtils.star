astUtils is package{
  private import ast;

-- Use this when ast is properly implemented
--  isUniv(<|for all ?V such that ?T |>) is some((V,T));
  isUniv(T) where isBinary(T,"such that") matches some((L,R)) and
  isUnary(L,"for all") matches some(V) is
    some((deComma(V),R));
  isUniv(_) default is none;

  isExists(T) where isBinary(T,"such that") matches some((L,R)) and
  isUnary(L,"exists") matches some(V) is
    some((deComma(V),R));
  isExists(_) default is none;

  deComma(T) where isBinary(T,",") matches some((L,R)) is list of { L;..deComma(R)};
  deComma(T) default is list of {T};

  deParen(asTuple(_,"()",list of {E})) is E;
  deParen(E) default is E;
}