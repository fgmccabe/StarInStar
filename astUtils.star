astUtils is package{
  private import ast;

  deComma(T) where isBinary(T,",") matches some((L,R)) is list of { L;..deComma(R)};
  deComma(T) default is list of {T};

  deParen(asTuple(_,"()",list of {E})) is E;
  deParen(E) default is E;
}