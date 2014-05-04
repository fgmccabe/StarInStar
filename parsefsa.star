parsefsa is package{
    import fsa;

  /*
    Parse a string into a FSA over characters
    A regular expression looks like:

     regexp ::= 
         .    -- any character
       | eof                              -- the end of file
       | [chars]    -- selection of characters
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



  }