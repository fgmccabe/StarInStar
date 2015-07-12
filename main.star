main is package{
  import errors
  import lexer
  import stdNames
  import operators
  import ast
  import opgrammar
  import canonical

  loadUri has type (uri)=>string
  fun loadUri(U) is string(__getUri(U))

  main has type (string)=>()
  prc main(Fl) do {
    def Uri is Fl as uri
    def Text is loadUri(Uri)
    def Toks is tokenize(Text,Uri,(0,1,0))

    def (Rest,Pr,T) is term(Toks,2000,standardOps)
    logMsg(info,"parse: $T")
--    logMsg(info,"internal: #(__display(T))")
    
    reportAllErrors()
  }

  _main has type (cons of string)=>()
  prc _main(L) do {
    for F in L do {
      main(F)
    }
  }
}