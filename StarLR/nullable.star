nullable is package{
  private import lrTypes;

  -- the set of non-terminals that may be nullable
  nullable has type (list of string,list of rule)=>list of string;
  nullable(nonTerms,rules) is valof{
    var N := list of [];
    var done := false;

    -- transitive closure ...
    while not done do {
      done := true;
      for nt in nonTerms and not nt in N do {
      	if rule{nt=nt;rhs = rhs} in rules and n in rhs implies n in N then{
      	  extend N with nt;
      	  done := false;		-- we have a new nullable non-terminal
      	}
      }
    }
    valis N;
  };
}