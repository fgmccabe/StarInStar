main is package{
  import errors;
  import lexer;
  import stdNames;
  import operators;
  import ast;
  import opgrammar;
  import canonical;

  loadUri has type (uri)=>string;
  loadUri(U) is string(__getUri(U));

  main has type (string)=>();
  main(Fl) do {
    Uri is Fl as uri;
    Text is loadUri(Uri);
    Toks is tokenize(Text,Uri,(0,1,0));

    (Rest,Pr,T) is term(Toks,2000,standardOps);
    logMsg(info,"parse: $T");
--    logMsg(info,"internal: #(__display(T))");
    
    reportAllErrors();
  }

  _main has type (cons of string)=>();
  _main(L) do {
    for F in L do {
      main(F)
    }
  }
}