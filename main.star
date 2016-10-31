main is package{
  import errors
  import lexer
  import stdNames
  import stdTypes
  import operators
  import ast
  import opgrammar
  import canonical
  import check

  loadUri has type (uri)=>string
  fun loadUri(U) is string(__getUri(U))

  main has type (string)=>()
  prc main(Fl) do {
    def Uri is Fl as uri
    def Toks is tokenize(Uri)

    def (Rest,Pr,T) is term(Toks,2000,standardOps)
    logMsg(info,"parse: $T")
--    logMsg(info,"internal: #(__display(T))")

    def prg is typeOfProgram(T,stdDict)
    logMsg(info,"canon: $prg")
    
    reportAllErrors()
  }

  _main has type (cons of string)=>()
  prc _main(L) do {
    for F in L do {
      main(F)
    }
  }
}