lr0 is package{
  private import lrTypes;
  private import nullable;

  private closeItems(Items,rules) is valof{
    var done := false;
    var I := Items;
    while not done do {
      done := true;
      for item{suffix=list of [X,.._]} in I do{
      	for rule{ruleNo=No;nt=X;rhs=Tau} in rules do {
      	  if not item{ruleNo=No;nt=X;prefix=list of [];suffix=Tau} in I then {
      	    done := false;
      	    extend I with item{ruleNo=No;nt=X;prefix=list of [];suffix=Tau};
      	  }
      	}
      }
    };
    valis I
  }

  lr0states(rules,start) is valof{
    var sNo := 0;
    var states := 
      list of [(sNo, closeItems(list of [
            	      item{ruleNo=0; nt = "<start>";
                    		prefix = list of []; suffix = list of [ start, "<eof>" ]}],rules))];
    var G := list of [];
    var stateDelta := states;
    var done := false;

    while not done do{			-- transitive closure
      done := true;

      var TT := states;
      var Next := list of {};

      for (C,I) in stateDelta do {
      	Xs is list of { unique X where item{suffix=list of [X,.._]} in I and X!="<eof>"};

      	for X in Xs do {
      	  NS is closeItems(
      	    list of {
      	      all item{ruleNo=n; nt=nt; prefix=list of [pr..,X]; suffix=B} where
                		item{ruleNo=n;nt=nt;prefix=pr;suffix=list of [X;..B]} in I
      	    },rules);

      	  if (D,NS) in TT then {
      	    if not (C,X,D) in G then
      	      G := list of [(C,X,D),..G];
      	  } else{
      	    sNo := sNo+1;		-- new state
      	    extend TT with (sNo,NS);
      	    extend Next with (sNo,NS);
      	    G := list of [(C,X,sNo),..G]
      	    done := false;
      	  }
      	}
      };
      states := TT;
      stateDelta := Next;
    };

    valis (states,G)
  };
}
