lrTtypes is package{

  -- this is an abstraction of the rule with an associated position 
  type item is item{
    ruleNo has type integer;		-- The rule number
    nt has type string;
    prefix has type list of string;	-- the item prefix
    suffix has type list of string;
  };

  implementation pPrint over item is {
    ppDisp(item{ruleNo=n;nt=N;prefix=P;suffix=S}) is ppSequence(0,
      	cons of [ppStr(n as string), ppStr(" : "), ppStr(N), ppStr("->"),
            	  showItems(P), ppStr("."), showItems(S), ppNl ]);
    private showItems(L) is ppSequence(0,
        	cons of { all ppStr(X) where X in L});
  }

  type tokenPriority is tA or lA(integer) or rA(integer) or nA(integer);
  
  type grAction is shiftTo(integer) or
    reduceBy(string,integer,integer) or -- nt, rule No, count
    accept(integer) or
    recoverError(list of string,integer,integer) or disabled(grAction);

  type rule is rule{
    ruleNo has type integer;
    nt has type string;
    rhs has type list of string;
--    orig has type quoted;		-- original rule. Used in final code generation
--    prior has type tokenPriority;
  };

}