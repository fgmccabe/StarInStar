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

private parseRegexp(text) is let{
    parseRE(Src) is parseSingle(Src,parseMore)

    parseSingle(['[','^',..T],Cx) is parseCharSet(T,[],fn(Chs,xT)=>Cx(xT,nonCharSet(Chs)))
    parseSingle(['[',..T],Cx) is parseCharSet(T,[],fn(Chs,xT)=>Cx(xT,charSet(Chs)))
    parseSingle(['.',..T],Cx) is Cx(T,anyChar)
    parseSingle(['(',..T],Cx) is parseSingle(T,fn(Ti,soFar)=>parseMore(Ti,soFar,fn(['\)',..Tx],final)=>Cx(Tx,final)))
    parseSingle([Ch,..T],Cx) is Cx(T,oneChar(Ch))

    parseMore([],soFar,Cx) => Cx([],soFar)
    parseMore(['\)',..T],soFar,Cx) => Cx(['\)',..T],soFar)
    parseMore(['*',..T],soFar,Cx) => parseMore(T,starFSA(soFar),Cx)
    parseMore(['+',..T],soFar,Cx) => parseMore(T,plusFSA(soFar),Cx)
    parseMore(['?',..T],soFar,Cx) => parseMore(T,optFSA(soFar),Cx)
    parseMore(['|',..T],soFar,Cx) => parseSingle(T,fn(xT,R)=>parseMore(xT,orS(soFar,R),Cx))
    parseMore([':',..T],soFar,Cx) => parseId(T,fn(xT,Id)=>parseMore(xT,bindVar(soFar,bind(Id)),Cx))

    parseCharSet([']',..T],Chars,Cont) is Cont(Chars,T)
    parseCharSet([X,'-',Y,..T],Chars,Cont) is parseCharSet(T,addToChars(X,Y,Chars),Cont)
    parseCharSet([X,..T],Chars,Cont) is parseCharSet(T,addChar(X,Chars),Cont)

    parseId([C,..R],Cont) where isIdentifierStart(C) is parseMoreId(R,[C],Cont)

    parseMoreId([C,..R],soFar,Cont) where isIdentifierChar(C) is parseMoreId(R,[C,..soFar],Cont)
    parseMoreId(T,soFar,Cont) is Cont(T,revImplode(soFar))
  }

  private isIdentifierStart(char(C)) is __isIdentifierStart(C);
  private isIdentifierChar(char(C)) is __isIdentifierPart(C);

  }