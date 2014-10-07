opgrammar is package{
  private import errors;
  private import lexer;
  private import operators;
  private import treemap;
  private import ast;

  term(Toks,priority,Ops) is 
      termRight(termLeft(Toks,priority,Ops),priority,Ops);

  termLeft(cons of [idTok("-",Lc),integerTok(I,Lc2),..Toks],_,Ops) is 
      (Toks,0,asInteger(mergeLocation(Lc,Lc2),-I));
  termLeft(cons of [idTok("-",Lc),longTok(I,Lc2),..Toks],_,Ops) is 
      (Toks,0,asLong(mergeLocation(Lc,Lc2),-I));
  termLeft(cons of [idTok("-",Lc),floatTok(I,Lc2),..Toks],_,Ops) is 
      (Toks,0,asFloat(mergeLocation(Lc,Lc2),-I));
  termLeft(cons of [idTok("-",Lc),decimalTok(I,Lc2),..Toks],_,Ops) is 
      (Toks,0,asDecimal(mergeLocation(Lc,Lc2),-I));
  termLeft(Tokens matching (cons of [idTok(Name,Lc),..Toks]),priority,Ops) is valof{
    if isPrefixOp(Name,Ops,priority) matches some(OpSpec) then {
      if OpSpec.priority<=priority then {
      	var (RToks,_,Right) is term(Toks,OpSpec.right,Ops);
      	valis (RToks,OpSpec.priority,
  	      oneApply(mergeLocation(Lc,locOf(Right)),asName(Lc,Name),Right))
      } else{
      	reportError("prefix operator $Name of priority $(OpSpec.priority) not permitted here",list of [Lc]);
      	valis (Toks,0,asName(Lc,Name));
      }
    } else 
    valis term0(Tokens,Ops)
  };
  termLeft(Toks,_,Ops) is term0(Toks,Ops);

  termRight((Toks matching (cons of [Hed,..Rest]),LeftPrior,Left),Prior,Ops) is 
      case Hed in {
      	terminal is (Toks,0,Left);
      	idTok(Op,Lc) where isRightBracket(Op,Ops) matches some(_) is (Toks,LeftPrior,Left);
      	idTok(Op,Lc) where isInfixOp(Op,Ops,Prior) matches some(InfSpec) and 
      	InfSpec.left>=LeftPrior and InfSpec.priority <= Prior is valof{
      	  if isPostfixOp(Op,Ops,Prior) matches some(Post) and 
      	  Post.left>=LeftPrior and Post.priority <= Prior then{
      	    var treatAsPostfix := false;
      	    case head(Rest) in {
      	      idTok(Nm,nLc) do {
            		if isRightBracket(Nm,Ops) matches some(_) then{
            		  treatAsPostfix := true
            		}
            		else if isPrefixOp(Nm,Ops,Prior) matches some(PrOp) then {
            		  treatAsPostfix := PrOp.priority>=InfSpec.priority
            		}
            		else if isInfixOp(Nm,Ops,Prior) matches some(NxOp) then 
            		  treatAsPostfix := NxOp.priority>=InfSpec.priority;
      	      }
      	      _ default do nothing;
      	    };
      	    if treatAsPostfix then
      	      valis termRight((Rest,Post.priority,
                oneApply(mergeLocation(locOf(Left),Lc),
        		    asName(Lc,Op),Left)),Prior,Ops)
      	    else{
      	      var (RToks,_,R) is term(Rest,InfSpec.right,Ops);
      	      valis termRight((RToks,InfSpec.priority,
      		     binApply(mergeLocation(locOf(Left),locOf(R)),
      		      asName(Lc,Op),Left,R)),Prior,Ops)
      	    }
      	  }
      	  else{
      	    -- infix only
      	    var (RToks,_,R) is term(Rest,InfSpec.right,Ops);
      	    valis termRight((RToks,InfSpec.priority,
      		   binApply(mergeLocation(locOf(Left),locOf(R)),
      		    asName(Lc,Op),Left,R)),Prior,Ops)
      	  }
      	};

      	idTok(Op,Lc) where isPostfixOp(Op,Ops,Prior) matches some(PostSpec) and 
          	PostSpec.left>=LeftPrior and PostSpec.priority <=Prior is 
          termRight((Rest,PostSpec.priority,
      		   oneApply(mergeLocation(locOf(Left),Lc),
      			 asName(Lc,Op),Left)),Prior,Ops);

      	_ default is (Toks,LeftPrior,Left);
      };

  term0(Toks matching (cons of [Hed,..Rest]),Ops) is case Hed in {
    integerTok(Ix,Lc) is (Rest,0,asInteger(Lc,Ix));
    longTok(Ix,Lc) is (Rest,0,asLong(Lc,Ix));
    floatTok(Dx,Lc) is (Rest,0,asFloat(Lc,Dx));
    decimalTok(Dx,Lc) is (Rest,0,asDecimal(Lc,Dx));
    charTok(Ch,Lc) is (Rest,0,asChar(Lc,Ch));
    stringTok(Str,Lc) is collectStringTokens(Str,Lc,Rest);
    regexpTok(Str,Lc) is (Rest,0,unary(Lc,"*regexp*",asString(Lc,Str)));
    _ default is valof{
      var (RToks,T0) is term00(Toks,Ops);
      valis termArgs(RToks,T0,Ops);
    }
  };

  term00(cons of [idTok(Id,Lc),..Toks],Ops) is 
      case Id in {
        "\#(" is valof{
          var (RToks,_,T) is term(Toks,2000,Ops);
          if RToks matches cons of [idTok(")\#",_),..RToks2] then
            valis (RToks2,T)
          else{
            reportError("expecting a \")\#\", opening \"\#(\" at $Lc",list of [Lc,peekLoc(RToks)]);
            valis (RToks,T)
          }
        };
        "\(" is parseParens(Lc,Toks,1200,Ops);
        "\{" is parseBraces(Lc,Toks,Ops);
        Nm default is valof{
          if isLeftBracket(Nm,Ops) matches some(BkSpec) then{
            valis parseBrackets(Lc,Toks,Ops,BkSpec);
          }
          else
            valis (Toks,asName(Lc,Nm));
        }
      };
  term00(cons of [Tk,..Toks],Ops) is valof{
    reportError("expecting an identifier, not $Tk",list of {tokenLoc(Tk)});
    valis term00(Toks,Ops);
  };

  private peekLoc(Toks) is tokenLoc(Toks[0]);

  checkForOperators(T,Ops) where isUnary(T,"\#") matches some(Meta) is valof{
    if isTernary(Meta,"infix") matches some((Lf,Md,Rt)) then {
      if Lf matches asString(_,Op) then{
      	if Md matches asInteger(_,Pr) then {
      	  if Rt matches asInteger(_,MinPrior) then
      	    valis defineInfix(Op,Pr-1,Pr,Pr-1,MinPrior,Ops)
      	  else
      	    reportError("expecting an integer, not $Rt",list of {locOf(Meta)});
      	}
      	else
      	  reportError("expecting an integer, not $Md",list of [locOf(Meta)]);
      }
      else
      	reportError("expecting a operator name (string), not $Lf",list of [locOf(Meta)]);
    	valis Ops
    }
    else if isBinary(Meta,"infix") matches some((L,R)) then {
      if L matches asString(_,Op) then{
      	if R matches asInteger(_,Pr) then
      	  valis defineInfix(Op,Pr-1,Pr,Pr-1,0,Ops)
      	else
      	  reportError("expecting an integer, not $R",list of [locOf(Meta)]);
      }
      else
      	reportError("expecting a operator name (string), not $L",list of [locOf(Meta)]);
    	valis Ops
    }
    else
      valis Ops
  }
  checkForOperators(T,Ops) default is Ops;

  parseParens(stLc,cons of [idTok(")",xLc),..Toks],_,_) is 
      (Toks,tple(mergeLocation(stLc,xLc),list of []));
  parseParens(stLc,Tokens,Priority,Ops) is let{
    parseParen(Toks,Els) is valof{
      var (cons of [HdTk,..TToks],_,T) is term(Toks,Priority,Ops);

      case HdTk in {
      	idTok(")",tlLc) do valis (TToks,tple(mergeLocation(stLc,tlLc),list of [Els..,T]));
      	idTok(",",_) do valis parseParen(TToks,list of [Els..,T]);
      	_ default do {
      	  reportError("expecting a ',' or ')', not $HdTk, '(' at $stLc",list of [tokenLoc(HdTk)]);
      	  valis parseParen(TToks,list of [Els..,T])
      	}
      }
    }
  } in parseParen(Tokens,list of [])

  parseBraces(stLc,cons of [idTok("}",xLc),..Tokens],_) is 
      (Tokens,asName(mergeLocation(stLc,xLc),"{}"));

  parseBraces(stLc,Tokens,Operators) is let{
    parseBrace(Toks,Els,Ops) is valof{
      var (RToks matching (cons of [HdTk,..TToks]),_,T) is term(Toks,1999,Ops);
      var Ops1 is checkForOperators(T,Ops);

      case HdTk in {
        idTok("\}",tlLc) do valis (TToks,block(mergeLocation(stLc,tlLc),list of [Els..,T]));
        idTok(";",_) do 
          if head(TToks) matches idTok("\}",tlLc) then
            valis (tail(TToks),block(mergeLocation(stLc,tlLc),list of [Els..,T]))
          else
            valis parseBrace(TToks,list of [Els..,T],Ops1);
        terminal do valis (RToks,block(mergeLocation(stLc,locOf(T)),list of [Els..,T]))
        _ default do {
          valis parseBrace(RToks,list of [Els..,T],Ops1)
        }
      }
    }
  } in parseBrace(Tokens,list of [],Operators);


  parseBrackets(stLc,cons of [idTok(Rgt,xLc),..Toks],_,Bkt) where Rgt=Bkt.right is
    (Toks,asTuple(mergeLocation(stLc,xLc),Bkt.op,list of []));
  parseBrackets(stLc,Tokens,Ops,Bkt) is let{
    var Rgt is Bkt.right;
    var Priority is Bkt.inPrior;

    parseBkt(Toks,Els) is valof{
      var (cons of [HdTk,..TToks],_,T) is term(Toks,Priority,Ops);

      case HdTk in {
      	idTok(R,tlLc) where R=Rgt do valis 
            	(TToks,asTuple(mergeLocation(stLc,tlLc),Bkt.op,list of [Els..,T]));
      	idTok(",",_) do valis parseBkt(TToks,list of [Els..,T]);
      	_ default do {
      	  reportError("expecting a ',' or '$Rgt', not $HdTk, '(' at $stLc",list of [tokenLoc(HdTk)]);
      	  valis parseBkt(TToks,list of [Els..,T])
      	}
      }
    }
  } in parseBkt(Tokens,list of []);


  termArgs(Tokens matching (cons of [Tk,..Tks]),Lhs,Ops) is case Tk in {
    idTok("(",Lc) is valof{ -- special handling needed for parens
      var (Toks,ArgsTuple) is parseParens(Lc,Tks,999,Ops);
      valis termArgs(Toks,asApply(mergeLocation(locOf(Lhs),locOf(ArgsTuple)),
	     Lhs,ArgsTuple),Ops);
    }
    idTok("{",Lc) is valof{ -- special handling needed for braces
      var (Toks,ArgsTuple) is parseBraces(Lc,Tks,Ops);
      valis termArgs(Toks,asApply(mergeLocation(locOf(Lhs),locOf(ArgsTuple)),
	     Lhs,ArgsTuple),Ops);
    }
    idTok(B,Lc) where isLeftBracket(B,Ops) matches some(BkSpec) is valof{
      var (Toks,ArgsTuple) is parseBrackets(Lc,Tks,Ops,BkSpec);
      valis termArgs(Toks,asApply(mergeLocation(locOf(Lhs),locOf(ArgsTuple)),
	     Lhs,ArgsTuple),Ops);
    }
    _ default is (Tokens,0,Lhs)
  };
      

  collectStringTokens(SoFar,Lc,cons of [stringTok(Str,LcN),..Toks]) is collectStringTokens(SoFar++Str,LcN,Toks);
  collectStringTokens(SoFar,Lc,Toks) default is (Toks,0,asString(Lc,SoFar));

  isRightBracketNext(cons of [idTok(N,Lc),.._],Ops) is isRightBracket(N,Ops) matches some(_);
  isRightBracketNext(_,_) default is false;

  head(sequence of [H,.._]) is H;
  tail(sequence of [_,..T]) is T;
}