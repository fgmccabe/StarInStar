parsefsa is package{
    import fsa;

  /*
    Parse a string into a FSA over characters
    A regular expression looks like:

     regexp ::= 
        .             -- any character
        | ^           -- start of the file
        | $           -- the end of file
        | [chars]     -- selection of characters
        | [^chars]    -- negative selection of characters
        | "echar*"    -- literal string
        | (regexp)    -- parenthesising
        | (regexp:Id) -- variable binding
        | regexp|regexp   -- disjunction
        | regexp regexp   -- concatenation of two regexps
        | regexp *
        | regexp +
        | regexp ?    -- optional re

     chars ::= char-char   -- range of characters
       | echar    -- regular or escape char

     echar ::= \escape   -- escape character
       | char    -- regular character

     escape ::= a    -- alarm
       | b    -- backspace
       | d    -- delete
       | e    -- escape
       | f    -- form feed
       | n    -- new line
       | r    -- carriage return
       | t    -- tab
       | v    -- vertical feed
       | oct    -- octal encoded character
       | char    -- other chars are quoted
  */

private fun parseRegexp(text) is let{
    fun parseRE(Src) is parseSingle(Src,parseMore)

    fun parseSingle([0c[,0c^,..T],Cx) is parseCharSet(T,[],(Chs,xT)=>Cx(xT,nonCharSet(Chs)))
     |  parseSingle([0c[,..T],Cx) is parseCharSet(T,[],(Chs,xT)=>Cx(xT,charSet(Chs)))
     |  parseSingle([0c.,..T],Cx) is Cx(T,anyChar)
     |  parseSingle([0c(,..T],Cx) is parseSingle(T,(Ti,soFar)=>parseMore(Ti,soFar,([0c\),..Tx],final)=>Cx(Tx,final)))
     |  parseSingle([Ch,..T],Cx) is Cx(T,oneChar(Ch))

    fun parseBinding([0c:,..T],Cx) is parseId(T,(xT,Id)=>parseParen(xT,())

    fun parseMore([],soFar,Cx) => Cx([],soFar)
     |  parseMore([0c\),..T],soFar,Cx) => Cx([0c\),..T],soFar)
     |  parseMore([0c*,..T],soFar,Cx) => parseMore(T,starFSA(soFar),Cx)
     |  parseMore([0c+,..T],soFar,Cx) => parseMore(T,plusFSA(soFar),Cx)
     |  parseMore([0c?,..T],soFar,Cx) => parseMore(T,optFSA(soFar),Cx)
     |  parseMore([0c|,..T],soFar,Cx) => parseSingle(T,(xT,R)=>parseMore(xT,orS(soFar,R),Cx))
     |  parseMore([0c:,..T],soFar,Cx) => parseId(T,(xT,Id)=>parseMore(xT,bindVar(soFar,bind(Id)),Cx))

    fun parseCharSet([0c],..T],Chars,Cont) is Cont(Chars,T)
     |  parseCharSet([X,0c-,Y,..T],Chars,Cont) is parseCharSet(T,addToChars(X,Y,Chars),Cont)
     |  parseCharSet([X,..T],Chars,Cont) is parseCharSet(T,addChar(X,Chars),Cont)

    fun parseId([C,..R],Cont) where isIdentifierStart(C) is parseMoreId(R,[C],Cont)

    fun parseMoreId([C,..R],soFar,Cont) where isIdentifierChar(C) is parseMoreId(R,[C,..soFar],Cont)
     |  parseMoreId(T,soFar,Cont) is Cont(T,revImplode(soFar))
  }

  private fun isIdentifierStart(integer(C)) is __isIdentifierStart(C);
  private fun isIdentifierChar(integer(C)) is __isIdentifierPart(C);

  }