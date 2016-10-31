chars is package{

  -- These function pick up the standard java notion of identifier
  fun isIdentifierStart(integer(C)) is __isIdentifierStart(C)
  fun isIdentifierChar(integer(C)) is __isIdentifierChar(C)
   
  isUnicodeIdentifier has type (string)=>boolean
  fun isUnicodeIdentifier(S) is checkIden(explode(S))

  private
  checkIden has type (list of integer) => boolean
  fun checkIden([F,..R]) where isIdentifierStart(F) is checkRest(R)
   |  checkIden(_) default is false

  private
  checkRest has type (list of integer) => boolean
  fun checkRest([]) is true
   |  checkRest([C,..R]) where isIdentifierStart(C) or isIdentifierChar(C) is checkRest(R)
   |  checkRest(_) default is false
}