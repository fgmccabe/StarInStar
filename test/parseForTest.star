parseForTest is package{
  import errors;
  import lexer;
  import operators;
  import opgrammar;
  import ast

	fun parseFile(File) is valof{
    def tokens is tokenize(File)
    def (Rest,Pr,T) is term(tokens,2000,standardOps);

    valis T
  }

  fun parseString(Text) is valof {
    def tokens is stringTokens(Text,someWhere{lineCount = 0; lineOffset=0; charCount = 0; length = size(Text)})

    def (_,_,T) is term(tokens,2000,standardOps)
    valis T
  }
}