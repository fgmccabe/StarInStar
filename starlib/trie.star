trie is package{
  type trie of (k,v) is trie{
    value has type option of v;
    dict has type dictionary of (k,trie of (k,v))
  }

  emptyTrie is trie{value=none;dict=dictionary of []}

  addToTrie(Ks,V,G) is let{
    addSeq([],T) is T substitute{value = some(V)}
    addSeq([F,..R],trie{value=Vl;dict=D}) is trie{value=Vl;
      dict=(D[F] matches DD ?
        D[with F->addSeq(R,DD)] |
        D[with F->addSeq(R,emptyTrie)])}
  } in addSeq(Ks,G)

  isTermTrie(G) is G.value!=none;

  trieVal(trie{value=some(X)}) is X;

  findInTrie(Ks,G) is let{
    inSeq([],T) is T.value;
    inSeq([F,..R],T) where T.dict[F] matches nT is inSeq(R,nT);
    inSeq(_,_) default is none;
  } in inSeq(Ks,G);

  removeFromTrie(Ks,G) is let{
    remSeq([],trie{dict=D}) is trie{value=none;dict=D}
    remSeq([F,..R],trie{value=Vl;dict=D}) is trie{value=Vl;
      dict=(D[F] matches DD ?
        D[with F->remSeq(R,DD)] |
        D)} 
  } in remSeq(Ks,G)

  hasFollow(K,G) is present G.dict[K];

  followTrie(K,G) is G.dict[K]

  implementation for all k,v such that iterable over trie of (k,v) determines v is {
    _iterate(T,F,S) is trieIterate(T,F,S);
  }

  private
  trieIterate(trie{value=some(V);dict=D},F,S) is 
    _checkTerate(F(V,S),F,D);
  trieIterate(trie{value=none;dict=D},F,S) is _iterate(D,fn(X,St) => _iterate(X,F,St),S);

  private
  _checkTerate(NoMore(X),_,_) is NoMore(X);
  _checkTerate(S,F,D) is _iterate(D,fn(X,St) => _iterate(X,F,St),S)

  implementation for all k,v such that indexable over trie of (k,v) determines (list of k,v) is {
    _index(Tr,Ks) is findInTrie(Ks,Tr)
    _set_indexed(Tr,Ks,V) is addToTrie(Ks,V,Tr)
    _delete_indexed(Tr,Ks) is removeFromTrie(Ks,Tr)
  }
}