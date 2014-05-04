tables is package{
  -- construct the transition table from the item sets
  private import lrTypes;

  private nonTerminals(rules) is 
    relation of {
      unique NT where rule{nt=NT} in rules
    };

  private terminals(rules,nonT) is 
    relation of {
      unique T where rule{rhs=R} in rules and T in R and not T in nonT
    };

  table((states,goSet),rules) is let{
    nTs is nonTerminals(rules);
    Ts is terminals(rules,nTs);
    AllTs is nTs++Ts;

    goto(Sno,Txs) is map of {all (X,Tgt) where (X,Tgt) in Txs and X in nTs};

    parseActions(Sno,Txs,Items) is valof{
      Red is redAction(Items);

      valis (map of { all (X,parseAction(X,Txs,Red)) where X in Ts}) ++
      acceptParse(Items)
    }

    parseAction(X,Txs,Red) is ((X,Tgt) in Txs ? list of {shiftTo(Tgt);..Red} | Red);

    redAction(Items) is list of { all reduceBy(Nt,rNo,size(prefix)) where 
	item{ruleNo=rNo;nt=Nt;prefix=prefix;suffix=list of {}} in Items};

    acceptParse(Items) is 
      map of { all ("<eof>",list of {accept(rNo)}) where item{ruleNo=rNo; suffix=list of {"<eof>"}} in Items};

    trans(Sno,Txs,Items) is (goto(Sno,Txs),parseActions(Sno,Txs,Items));

    transitions is list of {
      all (Sno,trans(Sno,relation of { all (X,T) where (Sno,X,T) in goSet},Items)) 
      where (Sno,Items) in states 
    };

  } in (map of { all (Sno,pActions) where (Sno,(_,pActions)) in transitions},
      map of { all (Sno,goStates) where (Sno,(goStates,_)) in transitions})
}

