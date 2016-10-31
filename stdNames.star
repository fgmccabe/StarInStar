stdNames is package{

  -- define the standard graphic identifiers
  type tokGraph is tokGraph{
    isFinal has type boolean
    dict has type dictionary of (integer,tokGraph)
  }

  prc addStdGrph("") do nothing
   |  addStdGrph(Name) do let{
        fun addName(nil,tokGraph{dict=D}) is tokGraph{isFinal=true;dict=D}
         |  addName(cons(Ch,Rest),tokGraph{isFinal=F;dict=D}) where D[Ch] has value Ex is valof{
              def ND is _set_indexed(D,Ch,addName(Rest,Ex))
              valis tokGraph{isFinal=F;dict=ND}
            }
         |  addName(cons(Ch,Rest),tokGraph{isFinal=F;dict=D}) is valof{
              def RD is addName(Rest,tokGraph{isFinal=false;dict=dictionary of []})
              valis tokGraph{isFinal=F;dict=_set_indexed(D,Ch,RD)}
            }
      } in { 
        StdNames := addName(explode(Name),StdNames)
      }
  
  var StdNames := tokGraph{isFinal=false;dict=dictionary of []}
  
  fun isLeadInChar(Ch) is present StdNames.dict[Ch]
  
  fun firstGraph(Ch) is StdNames.dict[Ch]
  
  isTermGraph has type (tokGraph)=>boolean
  fun isTermGraph(M) is M.isFinal
  
  isTermChar has type (integer,tokGraph)=>boolean
  fun isTermChar(Ch,M) is M.isFinal
  
  nextCharMap has type (integer,tokGraph)=>tokGraph
  fun nextCharMap(Ch,M) where M.dict[Ch] has value nxt is nxt
  
  isValidNextChar has type (integer,tokGraph)=>boolean
  fun isValidNextChar(Ch,M) is present M.dict[Ch]
  
  prc showStdGraph() do {
    logMsg(info,"grph is $StdNames")
  }

  private fun explode(string(S)) is __string_explode(S)
}
