nogood is package{
  private import location

  type good of T is good(T) or noGood(string,srcLoc)

  implementation for all T,E such that pPrint over good of T where pPrint over T is {
    ppDisp=showGood
  } using {
    fun showGood(good(G)) is ppSequence(0,[ppStr("good"),ppSpace,ppDisp(G)])
     |  showGood(noGood(N,L)) is ppSequence(0,[ppStr("noGood"),ppSpace,ppDisp(N),ppSpace,ppDisp(L)])
  }
  
  fun more(good(G),F) is F(G)
   |  more(noGood(M,L),F) is noGood(M,L)

  -- Combine an iteration 
  goodIterate has type for all i,o,x,y such that 
    (i,(x)=>good of y) => good of o where
      iterable over i determines x and
      sequence over o determines y
  fun goodIterate(L,F) is let{
    fun check(X,ContinueWith(good(SoFar))) is switch F(X) in {
          case good(G) is ContinueWith(good([SoFar..,G]))
          case noGood(M,Lc) is NoMore(noGood(M,Lc))
        }
     |  check(_,SoFar matching NoMore(_)) is SoFar
    fun unwrap(ContinueWith(X)) is X
     |  unwrap(NoMore(X)) is X

  } in unwrap(_iterate(L,check,ContinueWith(good([]))))

  goodSequence has type for all l,m,x such that 
    (l) => good of m where
    sequence over l determines good of x and
    sequence over m determines x
  fun goodSequence(S) is let {
    fun gdSeq([],soFar) is good(soFar)
     |  gdSeq([good(E),..R],soFar) is gdSeq(R,[soFar..,E])
     |  gdSeq([noGood(M,L),.._],_) is noGood(M,L) 
  } in gdSeq(S,[])

  implementation (computation) over good determines ((string,srcLoc)) is {
    fun _encapsulate(X) is good(X)
    fun _abort((M,L)) is noGood(M,L)
    fun _handle(good(X),_) is good(X)
     |  _handle(noGood(M,L),F) is F((M,L))
    fun _combine(good(X),F) is F(X)
     |  _combine(noGood(M,L),_) is noGood(M,L)
  }

  implementation execution over good is {
    fun _perform(good(X)) is X
  }

  implementation injection over (good,good) is {
    fun _inject(C) is C;
  }

  implementation injection over (IterState,good) is {
    fun _inject(NoMore(X)) is good(X)
     |  _inject(AbortIter(E matching exception(_,_,Lc))) is noGood("$E",Lc as srcLoc)
     |  _inject(NoneFound) is noGood("no answers",missing)
     |  _inject(ContinueWith(X)) is good(X)
  }

  implementation injection over (good, IterState) is {
    fun _inject(good(X)) is ContinueWith(X)
     |  _inject(noGood(M,L)) is AbortIter(exception("error",(M,L) cast any,noWhere))
  }
}