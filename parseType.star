parseType is package{
  private import ast;
  private import dict;
  private import types;

  parseType(asName(L,Nm),M) where M[Nm] matches Tp is Tp;
  parseType(