binomial is package{
  type binomial of t where comparable over t is 
      binomial(list of binTree of t);

  private type binTree of t where comparable over t is 
      binNd(integer,t,list of binTree of t);

  private 
  link(t1 matching binNd(R,x1,c1), t2 matching binNd(_,x2,c2)) is
      x1<=x2 ?
	binNd(R+1,x1,list of [t2,..c1])  |
      binNd(R+1,x2,list of [t1,..c2]);

  private
  rank(binNd(R,_,_)) is R;

  private
  root(binNd(_,T,_)) is T;

  private
  insTree(t,list of []) is list of [t];
  insTree(t,ts matching (list of [t1,..ts1])) is
      rank(t)<rank(t1) ?
	list of [t,..ts} |
      insTree(link(t,t1),ts1);

  private
  insrtNd(x,ts) is insTree(binNd(0,x,list of []),ts);

  private
  mrgeNds(ts,list of []) is ts;
  mrgeNds(list of [],ts) is ts;
  mrgeNds(ts1 matching (list of{t1,..ts11}), ts2 matching (list of [t2,..ts22])) is
      rank(t1)<rank(t2) ?
	list of [t1,..mrgeNds(ts11,ts2)] |
      rank(t1)>rank(t2) ?
	list of [t2,..mrgeNds(ts1,ts22)] |
      insTree(link(t1,t2),mrgeNds(ts11,ts22));

  private
  removeMinTree(list of [t]) is (t,list of []);
  removeMinTree(list of [t,..ts]) is valof{
    (t1,ts1) is removeMinTree(ts);
    valis root(t)<=root(t1) ?
      (t,ts) |
	(t1,list of [t,..ts1])
  };

  private
  findMin(T) is valof{
    (t,_) is removeMinTree(T);
    valis root(t);
  };

  private
  deleteMin(T) is valof{
    (binNd(_,X,ts1),ts2) is removeMinTree(T);
    valis mrgeNds(reverse(ts1),ts2);
  };

  implementation sequence over binomial of %t determines %t /*where comparable over %t*/ is let{
    binCons(H,binomial(ts)) is binomial(insTree(binNd(0,H,list of []),ts));
    binApnd(binomial(ts),H) is binomial(insTree(binNd(0,H,list of []),ts));
    binEmpty() from binomial(list of []);
    binPair(H,binomial(mrgeNds(ts1,ts2))) from binomial(T) where 
	removeMinTree(T) matches (binNd(_,H,ts1),ts2);
    binBack(binomial(mrgeNds(ts1,ts2)),H) from binomial(T) where 
	removeMinTree(T) matches (binNd(_,H,ts1),ts2);
    binNil() is binomial(list of [])
  } in {
    _cons = binCons;
    _apnd = binApnd;
    _empty = binEmpty;
    _pair = binPair;
    _back = binBack;
    _nil = binNil
  };

  implementation concatenate over binomial of %t where comparable over %t is{
    _concat(binomial(T1),binomial(T2)) is binomial(mrgeNds(T1,T2));
  };

  implementation iterable over binomial of %t determines %t is let{
    binIterate(list of [],_,St) is St;
    binIterate(_,_,NoMore(X)) is NoMore(X);
    binIterate(list of [T,..TS],F,St) is binIterate(TS,F,trIterate(T,F,St));

    trIterate(binNd(_,El,Ts),F,St) is binIterate(Ts,F,F(El,St));
  } in {
    _iterate(binomial(T),Fn,St) is binIterate(T,Fn,St)
  }

  implementation sizeable over binomial of %t is {
    isEmpty(binomial(list of [])) is true;
    isEmpty(_) default is false;

    size(binomial(L)) is countSize(L,0);

    private countSize(list of [],Cx) is Cx;
    countSize(list of [binNd(R,_,_),..TS],Cx) is countSize(TS,Cx+R+1);
  }

  implementation updateable over binomial of %t determines %t is {
    _extend(binomial(L),E) is binomial(insTree(binNd(0,E,list of []),L));
    _merge(B1,B2) is _concat(B1,B2);
    _delete(binomial(L),P) is binomial(deleteEls(L,P));
    _update(binomial(L),M,U) is binomial(updateEls(L,M,U));

    private deleteEls(list of [],_) is list of [];
    deleteEls(list of [binNd(R,El,SL),..TS],P) where El matches P() is valof{
      SL1 is deleteEls(SL,P);
      TS1 is deleteEls(TS,P);
      valis mrgeNds(SL1,TS1);
    }
    deleteEls(list of [binNd(R,El,SL),..TS],P) is valof{
      SL1 is deleteEls(SL,P);
      TS1 is deleteEls(TS,P);
      valis mrgeNds(insTree(binNd(0,El,list of []),SL1),TS1);
    }

    private updateEls(list of [],_,_) is list of [];
    updateEls(list of [binNd(_,El,SL),..TS],M,U) is valof{
      nEl is El matches M() ? U(El) | El; -- this might change the ordering of El, so we have to be slow
      SL1 is updateEls(SL,M,U);
      TS1 is updateEls(TS,M,U);
      valis mrgeNds(insTree(binNd(0,nEl,list of []),SL1),TS1)
    }
  }
}

