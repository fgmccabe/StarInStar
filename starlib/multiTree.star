multiTree is package{
	-- a kind of structured sequence where elements are either singly represented or sequenced

  type multiTree of t is 
    eTree
    or sTree(t)
    or mTree(list of multiTree of t);

  implementation for all t such that pPrint over multiTree of t where pPrint over t is {
		fun ppDisp(T) is ppSequence(2,cons of {ppStr("multiTree of {"); dispTree(T); ppStr("}")});
  } using {
		fun dispTree(eTree) is ppStr("")
		 |  dispTree(sTree(E)) is ppDisp(E)
		 |  dispTree(mTree(S)) is ppSequence(0,cons of { all dispTree(E) where E in S })
  };

  implementation for all t such that sequence over multiTree of t is {
		fun _cons(E,eTree) is sTree(E)
		 |  _cons(E,sTree(T)) is mTree(list of {sTree(E);sTree(T)})
		 |  _cons(E,mTree(L)) is mTree(list of {sTree(E);..L})

		fun _apnd(eTree,E) is sTree(E)
		 |  _apnd(sTree(T),E) is mTree(list of {sTree(T);sTree(E)})
		 |  _apnd(mTree(L),E) is mTree(list of {L..;sTree(E)})

		fun _nil() is eTree

		ptn _empty() from eTree

		ptn _pair(E,eTree) from sTree(E)
		 |  _pair(E,L) from mTree(list of [F,.._]) where F matches _pair(E,L)

		ptn _back(eTree,E) from sTree(E)
		 |  _back(L,E) from mTree(list of [_..,F]) where F matches _back(L,E)
	};

	implementation for all t such that sizeable over multiTree of t is {
		fun isEmpty(eTree) is true
		 |  isEmpty(mTree(L)) is allEmpty(L)
		 |  isEmtpy(_) default is false

		private
		fun allEmpty(list of {}) is true
		 |  allEmpty(list of [F,..L]) is isEmpty(F) and allEmpty(L)

		fun size(T) is count(T,0)

		private 
		fun count(C,eTree) is C
		 |  count(C,sTree(_)) is C+1
		 |  count(C,mTree(L)) is leftFold(count,C,L)
	};

    
	implementation for all t such that iterable over multiTree of t determines t is {
		fun _iterate(M,F,S) is iter(M,F,S);
	} using {
		fun iter(eTree,_,S) is S
		 |  iter(sTree(E),F,S) is F(E,S)
		 |  iter(mTree(L),F,S) is valof{
			    var Ix := 0;
			    def Mx is size(L);
			    var Sx := S;
			    while Ix<Mx do{
			    	Sx := iter(L[Ix],F,Sx);
			    	switch Sx in {
			    		case NoMore(_) do
			    			valis Sx;
			    		case _ default do
			    			Ix := Ix+1;
			    	}
			    };
			    valis Sx;
			  }
		};

	implementation for all t such that indexed_iterable over multiTree of t determines (integer,t) is {
		fun _ixiterate(M,F,S) is ixIter(M,F,0,S).1;
	} using {
		fun ixIter(eTree,_,Ix,S) is (Ix,S)
		 |  ixIter(sTree(E),F,Ix,S) is (Ix+1,F(Ix,Ea,S))
		 |  ixIter(mTree(L),F,I,S) is valof{
				  var Ix := I;
				  def Mx is size(L);
				  var Sx := S;
				  var i := 0;
				  while i<Mx do{
						(Ix,Sx) := ixIter(L[i],F,Ix,Sx);
						switch Sx in {
						  case NoMore(_) do
						    valis (Ix,Sx);
						  case _ default do i := i+1;
						}
				  };
				  valis (Ix,Sx);
				}
	}
}
