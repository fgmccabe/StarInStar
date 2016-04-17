operators is package{
  private import trie
  import stdNames

  type operatorStyle is prefixOp or infixOp or postfixOp

  type operSpec is operSpec{
    name has type string
    style has type operatorStyle
    left has type integer
    priority has type integer
    right has type integer
    minPriority has type integer
    minPriority default is 0
  }

  type bracketSpec is brackets{
    left has type string
    right has type string
    op has type string
    seqOp has type string
    seqOp default is ""
    inPrior has type integer
  }
  
  implementation pPrint over operSpec is {
    fun ppDisp(operSpec{name=N; style=prefixOp; minPriority=minPr; priority=Pr;right=rPr}) is
          ppSequence(0,cons of [ppStr(Pr=rPr?"\#assocPrefix":"\#prefix"),
                          	   ppStr("("),ppStr(display(N)),ppStr(","),ppStr(Pr as string),showMinPr(minPr),ppStr(")")])
     |  ppDisp(operSpec{name=N; style=infixOp; minPriority=minPr; left=lPr; priority=Pr;right=rPr}) is
        	ppSequence(0,cons of [ppStr(Pr=rPr?"\#right" : Pr=lPr? "\#left" : "\#infix"),
                                ppStr("("), ppStr(display(N)), ppStr(","), ppStr(Pr as string), showMinPr(minPr), ppStr(")")])
     |  ppDisp(operSpec{name=N; style=postfixOp; minPriority=minPr; left=lPr;priority=Pr}) is
        	ppSequence(0,cons of [ ppStr(Pr=lPr?"\#assocPostfix" : "\#postfix"), ppStr("("), ppStr(display(N)), ppStr(","), ppStr(Pr as string),
              	   showMinPr(minPr), ppStr(")")])
    private
    fun showMinPr(0) is ppSequence(0,cons of [])
     |  showMinPr(Pr) is ppSequence(0,cons of [ppStr(","), ppStr(Pr as string) ])
  }
  
  implementation pPrint over bracketSpec is {
    fun ppDisp(brackets{left=L;right=R;op=Op;seqOp=S;inPrior=I}) is 
          ppSequence(0,cons of [ ppStr("\#pair("), ppStr(display(L)), ppStr(","), ppStr(display(R)), ppStr(","),
                                  ppStr(display(Op)), ppStr(","), ppStr(I as string),
                                  S=""?ppSequence(0,nil):ppSequence(0,cons of [ppStr(","),ppStr(display(S))]),
                                  ppStr(")") ])
  }
  
  type operators is operators{
    ops has type dictionary of (string, dictionary of (operatorStyle,operSpec))
    multiops has type trie of (string, string)
    brackets has type dictionary of (string, bracketSpec)
  }
  
  implementation pPrint over operators is {
    fun ppDisp(Ops) is ppSequence(2,
    	  interleave(showOperators(Ops.ops)++showBrackets(Ops.brackets),
                    ppSequence(0,cons of [ppStr(";"),ppNl])))
  } using {
    fun showOperators(Ops) is cons of { all ppDisp(Op) where AOps in Ops and Op in AOps }
    fun showBrackets(Bkts) is cons of { all ppDisp(Bk) where Bk in Bkts }
  }
  
  fun interleave(cons of [H,..T],I) is cons of [H,..nextLeave(T,I)]
   |  interleave(cons of [],_) is cons of []
  
  private
  fun nextLeave(cons of [H,..T],I) is cons of [I,H,..nextLeave(T,I)]
   |  nextLeave(cons of [],_) is cons of []
  
  private
  checkMultiWord has type (string,trie of (string,string))=>trie of (string,string)
  fun checkMultiWord(S,ops) is valof {
        if findstring(S," ",0)>=0 then {
          def pieces is splitString(S," ")
          valis addToTrie(pieces,S,ops)
        } else{
          if not isUnicodeIdentifier(S) then
            addStdGrph(S)
          valis addToTrie(list of [S],S,ops)
        }
      }

  private
  splitOp has type (string)=>list of string
  fun splitOp(S) is valof{
        if findstring(S," ",0)>=0 then
          valis splitString(S," ")
        else
          valis list of [S]
      }
    
  definePrefix has type (string,integer,integer,integer,operators)=>operators
  fun definePrefix(op, priority, right, minPr, ops) is valof {
    var Opers := ops.ops
    var Defs := Opers[op] has value Dict ? Dict : dictionary of []
    Defs[prefixOp] := operSpec{
      name = op
      style = prefixOp
      left = nonInteger
      priority = priority
      right = right
      minPriority = minPr
    }
    Opers[op] := Defs
    valis ops substitute { ops = Opers; multiops = checkMultiWord(op,ops.multiops) }
  }
    
  fun defineNonAssocPrefix(op,priority,ops) is
    definePrefix(op,priority,priority-1,0,ops)
    
  fun defineAssocPrefix(op,priority,ops) is
    definePrefix(op,priority,priority,0,ops)
    
  defineInfix has type (string,integer,integer,integer,integer,operators)=>operators;    
  fun defineInfix(op, left, priority, right, minPr, ops) is valof {
    var Opers := ops.ops
    var Defs :=  Opers[op] has value Def ? Def : dictionary of []
    Defs[infixOp] := operSpec{
      name = op
      style = infixOp
      left = left
      priority = priority
      right = right
      minPriority = minPr
    }
    Opers[op] := Defs
      
    valis ops substitute { ops = Opers; multiops = checkMultiWord(op,ops.multiops) }
  }
  
  fun defineLeft(op,priority,ops) is
    defineInfix(op,priority,priority,priority-1,0,ops)
    
  fun defineNonAssocInfix(op,priority,ops) is
    defineInfix(op,priority-1,priority,priority-1,0,ops)
    
  fun defineRight(op,priority,ops) is
    defineInfix(op,priority-1,priority,priority,0,ops)
    
  definePostfix has type (string,integer,integer,integer,operators)=>operators
  fun definePostfix(op, left, priority, minPr, ops) is valof {
    var Opers := ops.ops
    var Defs :=  Opers[op] has value Def ? Def : dictionary of []
    Defs[postfixOp] := operSpec{
      name = op
      style = prefixOp
      left = left
      priority = priority
      right = nonInteger
      minPriority = minPr
    }
    Opers[op] := Defs
    valis ops substitute { ops = Opers; multiops = checkMultiWord(op,ops.multiops) }
  }
    
  fun defineNonAssocPostfix(op,priority,ops) is
    definePostfix(op,priority-1,priority,0,ops)

  fun defineToken(tk,ops) is ops substitute { multiops = checkMultiWord(tk,ops.multiops) }
    
  defineBktPair has type (string,string,string,string,integer,operators) => operators
  fun defineBktPair(Left,Right,Op,Seq,Inner,Ops) is valof{
    var Bkts := Ops.brackets
      
    def BkSpec is brackets{ left=Left; right=Right; op=Op; seqOp=Seq; inPrior=Inner}
      
    Bkts[Left] := BkSpec
    Bkts[Right] := BkSpec
    Bkts[Op] := BkSpec
      
    addStdGrph(Left)
    addStdGrph(Right)

    valis Ops substitute { brackets = Bkts}
  }

  def standardOps is valof{
    var opTable := operators{
      ops = dictionary of []
      multiops = emptyTrie
      brackets = dictionary of []
    }

    opTable := defineRight(";",2000,opTable)
    opTable := defineNonAssocPostfix(";",2000,opTable)
    opTable := defineNonAssocPrefix("#",1350,opTable)
    opTable := defineNonAssocInfix(":-",1347,opTable)
    opTable := defineNonAssocInfix("-->",1347,opTable)
    opTable := defineNonAssocInfix("==>",1347,opTable)
    opTable := defineRight(":|",1345,opTable)
    opTable := defineRight(":&",1344,opTable)
    opTable := defineNonAssocPrefix(":!",1343,opTable)
    opTable := defineNonAssocInfix("\#\#",1342,opTable)
    opTable := defineNonAssocInfix("::",1341,opTable)
    opTable := defineNonAssocInfix("|*",1340,opTable)
    opTable := defineNonAssocInfix(":*",1340,opTable)
    opTable := defineNonAssocInfix(":+",1340,opTable)
    opTable := defineNonAssocInfix(";*",1340,opTable)
    opTable := defineAssocPrefix("private",1320,opTable)
    opTable := defineNonAssocPrefix("def",1300,opTable)
    opTable := defineNonAssocPrefix("java",1300,opTable)
    opTable := defineNonAssocPrefix("var",1300,opTable)
    opTable := defineNonAssocPrefix("contract",1300,opTable)
    opTable := defineNonAssocPrefix("fun",1300,opTable)
    opTable := defineNonAssocPrefix("open",1300,opTable)
    opTable := defineNonAssocPrefix("prc",1300,opTable)
    opTable := defineNonAssocPrefix("on",1300,opTable)
    opTable := defineNonAssocPrefix("implementation",1300,opTable)
    opTable := defineNonAssocPrefix("ptn",1300,opTable)
    opTable := defineNonAssocPrefix("case",1290,opTable)
    opTable := defineRight("|",1290,opTable)
    opTable := defineNonAssocPrefix("type",1250,opTable)
    opTable := defineNonAssocInfix("counts as",1200,opTable)
    opTable := defineRight("else",1200,opTable)
    opTable := defineNonAssocInfix("is",1200,opTable)
    opTable := defineRight("do",1200,opTable)
    opTable := defineNonAssocPrefix("remove",1200,opTable)
    opTable := defineNonAssocInfix("then",1180,opTable)
    opTable := defineNonAssocPrefix("if",1175,opTable)
    opTable := defineNonAssocPrefix("while",1175,opTable)
    opTable := defineNonAssocPrefix("for",1175,opTable)
    opTable := defineNonAssocPrefix("yield",1150,opTable)
    opTable := defineNonAssocInfix("to",1130,opTable)
    opTable := defineNonAssocInfix("from",1130,opTable)
    opTable := defineNonAssocInfix(":=",1120,opTable)
    opTable := defineNonAssocPrefix("perform",1120,opTable)
    opTable := defineNonAssocPrefix("merge",1100,opTable)
    opTable := defineNonAssocPrefix("extend",1100,opTable)
    opTable := defineNonAssocPrefix("notify",1100,opTable)
    opTable := defineNonAssocPostfix("default",1100,opTable)
    opTable := defineNonAssocPrefix("assert",1100,opTable)
    opTable := defineNonAssocPrefix("valis",1100,opTable)
    opTable := defineNonAssocPrefix("try",1100,opTable)
    opTable := defineNonAssocPrefix("update",1100,opTable)
    opTable := defineNonAssocPrefix("delete",1100,opTable)
    opTable := defineNonAssocPrefix("ignore",1100,opTable)
    opTable := defineNonAssocInfix("//",1100,opTable)
    opTable := defineNonAssocInfix(",..",1099,opTable)
    opTable := defineNonAssocInfix("..,",1098,opTable)
    opTable := defineNonAssocInfix("catch",1050,opTable)
    opTable := defineNonAssocPrefix("request",1050,opTable)
    opTable := defineNonAssocInfix("with",1050,opTable)
    opTable := defineNonAssocInfix("hastype",1020,opTable)
    opTable := defineNonAssocPrefix("switch",1020,opTable)
    opTable := defineNonAssocInfix("has type",1020,opTable)
    opTable := defineRight("such that",1010,opTable)
    opTable := defineAssocPrefix("exists",1005,opTable)
    opTable := defineAssocPrefix("for all",1005,opTable)
    opTable := defineRight(",",1000,opTable)
    opTable := defineNonAssocInfix("default",1000,opTable)
    opTable := defineNonAssocPrefix("abort with",1000,opTable)
    opTable := defineNonAssocPrefix("query",1000,opTable)
    opTable := defineNonAssocPrefix("import",1000,opTable)
    opTable := defineNonAssocPrefix("memo",999,opTable)
    opTable := defineNonAssocPrefix("without",999,opTable)
    opTable := defineNonAssocInfix("computation",999,opTable)
    opTable := defineNonAssocInfix("./",999,opTable)
    opTable := defineNonAssocPrefix("with",999,opTable)
    opTable := defineRight(":",960,opTable)
    opTable := defineNonAssocPostfix(":",960,opTable)
    opTable := defineLeft("group by",960,opTable)
    opTable := defineNonAssocPrefix("when",950,opTable)
    opTable := defineRight("?",950,opTable)
    opTable := defineRight("~",950,opTable)
    opTable := defineNonAssocInfix("order descending by",950,opTable)
    opTable := defineNonAssocPrefix("waitfor",950,opTable)
    opTable := defineNonAssocPrefix("spawn",950,opTable)
    opTable := defineNonAssocInfix("order by",950,opTable)
    opTable := defineNonAssocInfix("descending by",950,opTable)
    opTable := defineNonAssocInfix("where",940,opTable)
    opTable := defineRight("otherwise",930,opTable)
    opTable := defineRight("or",930,opTable)
    opTable := defineRight("implies",920,opTable)
    opTable := defineRight("and",920,opTable)
    opTable := defineRight("=>",910,opTable)
    opTable := defineRight("\$=>",910,opTable)
    opTable := defineNonAssocPrefix("not",910,opTable)
    opTable := defineRight("<=>",910,opTable)
    opTable := defineNonAssocPrefix("let",909,opTable)
    opTable := defineLeft("using",908,opTable)
    opTable := defineNonAssocInfix("in",908,opTable)
    opTable := defineNonAssocInfix("'s",907,opTable)
    opTable := defineRight("'n",906,opTable)
    opTable := defineRight("or else",900,opTable)
    opTable := defineNonAssocInfix("matches",900,opTable)
    opTable := defineNonAssocInfix("!=",900,opTable)
    opTable := defineNonAssocInfix("<",900,opTable)
    opTable := defineNonAssocInfix("=",900,opTable)
    opTable := defineNonAssocInfix(">",900,opTable)
    opTable := defineNonAssocInfix("substitute",900,opTable)
    opTable := defineNonAssocInfix("=<",900,opTable)
    opTable := defineNonAssocInfix("<=",900,opTable)
    opTable := defineNonAssocPrefix("ref",900,opTable)
    opTable := defineNonAssocPrefix("kind",900,opTable)
    opTable := defineNonAssocPostfix("is tuple",900,opTable)
    opTable := defineNonAssocInfix("->",900,opTable)
    opTable := defineNonAssocInfix("has kind",900,opTable)
    opTable := defineNonAssocInfix("bound to",900,opTable)
    opTable := defineNonAssocInfix("has value",900,opTable)
    opTable := defineNonAssocInfix(">=",900,opTable)
    opTable := defineRight("implements",900,opTable)
    opTable := defineNonAssocInfix("on",900,opTable)
    opTable := defineRight("over",900,opTable)
    opTable := defineNonAssocInfix("instance of",900,opTable)
    opTable := defineNonAssocInfix("determines",895,opTable)
    opTable := defineRight("++",850,opTable)
    opTable := defineRight("of",840,opTable)
    opTable := defineNonAssocPrefix("alias of",840,opTable)
    opTable := defineNonAssocPrefix("reduction",830,opTable)
    opTable := defineNonAssocInfix("matching",800,opTable)
    opTable := defineLeft("+",720,opTable)
    opTable := defineLeft("-",720,opTable)
    opTable := defineLeft("%",700,opTable)
    opTable := defineLeft("*",700,opTable)
    opTable := defineLeft("/",700,opTable)
    opTable := defineNonAssocInfix("**",650,opTable)
    opTable := defineNonAssocPrefix("valof",500,opTable)
    opTable := defineNonAssocInfix("on abort",475,opTable)
    opTable := defineNonAssocInfix("as",420,opTable)
    opTable := defineNonAssocPrefix("unique",400,opTable)
    opTable := defineNonAssocPrefix("any of",400,opTable)
    opTable := defineNonAssocPrefix("anyof",400,opTable)
    opTable := defineNonAssocPrefix("all",400,opTable)
    opTable := defineNonAssocInfix("@@",200,opTable)
    opTable := defineNonAssocInfix("@",200,opTable)
    opTable := defineNonAssocInfix("\#@",200,opTable)
    opTable := defineLeft(".",175,opTable)
    opTable := defineLeft("?.",175,opTable)
    opTable := defineNonAssocPrefix("!",150,opTable)
    opTable := defineNonAssocPrefix("+",100,opTable)
    opTable := defineNonAssocPrefix("-",100,opTable)
    opTable := defineNonAssocPrefix("$",75,opTable)
    opTable := defineNonAssocPrefix("%",75,opTable)
    opTable := defineNonAssocPrefix("?",75,opTable)
    opTable := defineNonAssocPrefix(".",75,opTable)
    opTable := defineNonAssocPrefix("%%",75,opTable)
    opTable := defineNonAssocPrefix("\#$",50,opTable)
    opTable := defineNonAssocPrefix("\#*",50,opTable)
    opTable := defineRight("\#+",50,opTable)
    opTable := defineNonAssocPrefix("\#:",50,opTable)
    opTable := defineNonAssocPrefix("\$\$",50,opTable)
    opTable := defineRight("\$\$",50,opTable)
    opTable := defineNonAssocPrefix("\#~",50,opTable)

    opTable := defineBktPair("(",")","()",",",1200,opTable)
    opTable := defineBktPair("{","}","{}",";",2000,opTable)
    opTable := defineBktPair("[","]","[]","",1000,opTable)
    opTable := defineBktPair("\#(",")\#","","",2000,opTable)
    opTable := defineBktPair("\#<",">\#","\#<>","",2000,opTable)
    opTable := defineBktPair("<|","|>","quote","",2000,opTable)

    valis opTable; 
  }

  isPrefixOp has type (string,operators,integer) => option of operSpec
  fun isPrefixOp(Nm,Ops,Pr) where Ops.ops[Nm] has value Specs and Specs[prefixOp] has value prOp is valof{
      if prOp.minPriority=<Pr then
        valis some(prOp)
      else
        valis none
    }
   |  isPrefixOp(Nm,Ops,Pr) default is none
    
  fun isInfixOp(Nm,Ops,Pr) where Ops.ops[Nm] has value Specs and Specs[infixOp] has value opSpec is valof{
        if opSpec.minPriority=<Pr then
          valis some(opSpec)
        else
          valis none
      }
   |  isInfixOp(Nm,Ops,Pr) default is none
    
  fun isPostfixOp(Nm,Ops,Pr) where Ops.ops[Nm] has value Specs and Specs[postfixOp] has value opSpec is valof{
        if opSpec.minPriority=<Pr then
          valis some(opSpec)
        else
          valis none
      }
   |  isPostfixOp(Nm,Ops,Pr) default is none
    
  fun isLeftBracket(B,ops) where ops.brackets[B] has value opBrackets and opBrackets.left=B is some(opBrackets)
   |  isLeftBracket(_,_) default is none
    
  fun isRightBracket(B,ops) where ops.brackets[B] has value opBrackets and opBrackets.right=B is some(opBrackets)
   |  isRightBracket(_,_) default is none

  fun isBracket(B,ops) where ops.brackets[B] has value opBrackets and opBrackets.op=B is some(opBrackets)
   |  isBracket(_,_) default is none

  fun isOperator(Nm,Ops,Pr) where Ops.ops[Nm] has value opSpecs is valof{
        for Spec in opSpecs do {
          if Spec.minPriority=<Pr then
          	valis true
        }
        valis false
      }
   |  isOperator(_,_,_) default is false
}
