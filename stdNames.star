stdNames is package{

  -- define the standard graphic identifiers
  type tokGraph is tokGraph{
    isFinal has type boolean;
    dict has type dictionary of (char,tokGraph)
  };

  addStdGrph("") do nothing;
  addStdGrph(Name) do let{
    addName(nil,tokGraph{dict=D}) is tokGraph{isFinal=true;dict=D};
    addName(cons(Ch,Rest),tokGraph{isFinal=F;dict=D}) where present D[Ch] is valof{
      ND is _set_indexed(D,Ch,addName(Rest,D[Ch]));
      valis tokGraph{isFinal=F;dict=ND}
    }
    addName(cons(Ch,Rest),tokGraph{isFinal=F;dict=D}) is valof{
      RD is addName(Rest,tokGraph{isFinal=false;dict=dictionary of {}});
      valis tokGraph{isFinal=F;dict=_set_indexed(D,Ch,RD)};
    };
  } in { 
    StdNames := addName(explode(Name),StdNames);
  };
  
  var StdNames := tokGraph{isFinal=false;dict=dictionary of {}};
  
  isLeadInChar(Ch) is present StdNames.dict[Ch];
  
  firstGraph(Ch) is StdNames.dict[Ch];
  
  isTermGraph has type (tokGraph)=>boolean;
  isTermGraph(M) is M.isFinal;
  
  isTermChar has type (char,tokGraph)=>boolean;
  isTermChar(Ch,M) is M.isFinal;
  nextCharMap has type (char,tokGraph)=>tokGraph;
  nextCharMap(Ch,M) is M.dict[Ch];
  
  isValidNextChar has type (char,tokGraph)=>boolean;
  isValidNextChar(Ch,M) is present M.dict[Ch];
  
  showStdGraph() do {
    logMsg(info,"grph is $StdNames");
  };

  private explode(string(S)) is __string_explode(S);
}
