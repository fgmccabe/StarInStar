collections is package{
  contract collections over t determines e is {
    emptySet has type t;
    add_element has type (t,e)=>t;
    remove_element has type (t,e)=>t;
    contains_element has type (t,e)=>boolean;
  }

  type set of t where equality over t is set(dictionary of (t,()));

  implementation for all k such that collections over set of k determines k is {
    def emptySet is set(dictionary of []);
    fun add_element(set(S),K) is set(S[with K->()])
    fun remove_element(set(S),K) is set(S[without K])
    fun contains_element(set(S),K) is present S[K];
  }

  implementation for all k such that sequence over set of k determines k is {
    fun _cons(E,set(D)) is set(D[with E->()])
    fun _apnd(set(D),E) is set(D[with E->()])
    fun _nil() is emptySet
    ptn _empty() from X where X = emptySet
    ptn _pair((raise "not implemented"),(raise "not implemented")) from X;
    ptn _back((raise "not implemented"),(raise "not implemented")) from X;
  }

  implementation for all ky such that iterable over set of ky determines ky is {
    _iterate = setIterate
  } using {
    fun setIterate(set(D),F,S) is _ixiterate(D,(Ky,Vl,St)=>F(Ky,St),S)
  }

  implementation for all ky such that pPrint over set of ky where pPrint over ky is {
    fun ppDisp(D) is ppSequence(0,cons of [ppStr("{"),showContent(D),ppStr("}")])
  } using {
    fun showContent(D) is ppSequence(0,cons of {all ppDisp(E) where E in D})
  }

  implementation sets over set of %e is {
    fun set(X) union set(Y) is set(X++Y)
    fun set(X) intersect set(Y) is set(dictionary of { all K->() where K->() in X and K->() in Y})
    fun set(X) complement set(Y) is set(dictionary of {all K->() where K->() in X and not present Y[K]})
  }

  implementation mappable over set is {
    map = setMap
  } using {
    fun setMap(Fn,set(D)) is set(dictionary of { all Fn(Ky)->() where Ky->_ in D})
  }
}
  