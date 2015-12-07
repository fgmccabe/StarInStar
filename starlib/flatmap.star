flatmap is package{
  flatMap has type for all e,f,k,l,m such that
    ((e)=>f,l)=>m where sequence over l determines k and sequence over k determines e and sequence over m determines f
  fun flatMap(F,Items) is let{
    fun flMap([],soFar) is soFar
     |  flMap([L,..R],soFar) is flMap(R,fMap(L,soFar))
    fun fMap([],soFar) is soFar
     |  fMap([E,..R],soFar) is fMap(R,[soFar..,F(E)])
  } in flMap(Items,[])

  zip has type for all e,f such that (list of e,list of f) => list of ((e,f))
  fun zip([],[]) is []
   |  zip([E,..Erest],[O,..Orest]) is [(E,O),..zip(Erest,Orest)]
}