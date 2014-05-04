import worksheet
worksheet{
  import lrTypes;
  import lr0;
  import tables;
  import driver;

  -- set up a simple grammar
  /*
   * E -> E * B
   * E -> E + B
   * E -> B
   * B -> 0
   * B -> 1
   */

  eRules0 is list of {
    rule{ruleNo = 0; nt = "<start>"; rhs = list of {"E";"<eof>"}};
    rule{ruleNo = 1; nt = "E"; rhs = list of {"E"; "*"; "B"}};
    rule{ruleNo = 2; nt = "E"; rhs = list of {"E"; "+"; "B"}};
    rule{ruleNo = 3; nt = "E"; rhs = list of {"B"}};
    rule{ruleNo = 4; nt = "B"; rhs = list of {"0"}};
    rule{ruleNo = 5; nt = "B"; rhs = list of {"1"}};
  };

  (a0,g0) is table(lr0states(eRules0,"E"),eRules0);

  tokens0 is list of {"1"; "+"; "1"; "<eof>"};
  show driver(a0,g0)(tokens0);

  -- try the glr driver too

  show glrDriver(a0,g0)(tokens0);

  -- set up a shift/reduce conflict

  /*
   * E -> 1 E
   * E -> 1
   */

  eRules1 is list of {
    rule{ruleNo=0; nt = "<start>"; rhs = list of {"E";"<eof>"}};
    rule{ruleNo=1; nt = "E"; rhs = list of {"1";"E"}};
    rule{ruleNo=2; nt = "E"; rhs = list of {"1"}};
  };

  show table(lr0states(eRules1,"E"),eRules1);

  -- set up a reduce/reduce conflict
  /*
   * E -> A 1
   * E -> B 2
   * A -> 1
   * B -> 1
   */

  eRules2 is list of {
    rule{ruleNo=0; nt = "<start>"; rhs = list of {"E";"<eof>"}};
    rule{ruleNo=1; nt = "E"; rhs = list of {"A";"1"}};
    rule{ruleNo=2; nt = "E"; rhs = list of {"B";"2"}};
    rule{ruleNo=3; nt = "A"; rhs = list of {"1"}};
    rule{ruleNo=4; nt = "B"; rhs = list of {"1"}};
  };

  show table(lr0states(eRules2,"E"),eRules2);

}
