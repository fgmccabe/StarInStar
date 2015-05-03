opgrammar is package{
  private import errors;
  private import lexer;
  private import operators;
  private import trie;
  private import leftRight;
  private import ast;

  term(Toks,priority,Ops) is termRight(termLeft(Toks,priority,Ops),priority,Ops);

  termLeft(Toks,priority,Ops) where nxtTok(Toks,Ops) matches (Tk,nToks) is 
    case Tk in {
      idTok(Name,Lc) is valof{
        if isPrefixOp(Name,Ops,priority) matches some(OpSpec) then {
          if OpSpec.priority<=priority then {
            var (RToks,_,Right) is term(nToks,OpSpec.right,Ops);
            valis (RToks,OpSpec.priority,
              oneApply(mergeLocation(Lc,locOf(Right)),asName(Lc,Name),Right))
          } else{
            reportError("prefix operator $Name of priority $(OpSpec.priority) not permitted here",list of [Lc]);
            valis (nToks,0,asName(Lc,Name));
          }
        } else
          valis term0(Toks,Ops)
      }
      T default is term0(Toks,Ops);
   }

  termRight((Toks,LeftPrior,Left),Prior,Ops) where nxtTok(Toks,Ops) matches (Hed,Rest) is 
    case Hed in {
      terminal is (Toks,0,Left);
      idTok(Op,Lc) where isRightBracket(Op,Ops) matches some(_) is (Toks,LeftPrior,Left);
      idTok(Op,Lc) where isInfixOp(Op,Ops,Prior) matches some(InfSpec) and 
            InfSpec.left>=LeftPrior and InfSpec.priority <= Prior is valof{
              if isPostfixOp(Op,Ops,Prior) matches some(Post) and 
                Post.left>=LeftPrior and Post.priority <= Prior then{
          var treatAsPostfix := false;

          if nxtTok(Rest,Ops) matches (idTok(Nm,nLc),_) then{
            if isRightBracket(Nm,Ops) matches some(_) then{
              treatAsPostfix := true
            }
            else if isPrefixOp(Nm,Ops,Prior) matches some(PrOp) then {
              treatAsPostfix := PrOp.priority>=InfSpec.priority
            }
            else if isInfixOp(Nm,Ops,Prior) matches some(NxOp) then 
              treatAsPostfix := NxOp.priority>=InfSpec.priority;
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

  term0(Toks,Ops) where nxtTok(Toks,Ops) matches (Hed,Rest) is case Hed in {
    integerTok(Ix,Lc) is (Rest,0,asInteger(Lc,Ix));
    longTok(Ix,Lc) is (Rest,0,asLong(Lc,Ix));
    floatTok(Dx,Lc) is (Rest,0,asFloat(Lc,Dx));
    decimalTok(Dx,Lc) is (Rest,0,asDecimal(Lc,Dx));
    charTok(Ch,Lc) is (Rest,0,asChar(Lc,Ch));
    stringTok(Str,Lc) is collectStringTokens(Str,Lc,Rest,Ops);
    interpolatedString(Els,Lc) is (Rest,0,parseInterpolation(Els,Lc,Ops))
    regexpTok(Str,Lc) is (Rest,0,unary(Lc,"*regexp*",asString(Lc,Str)));
    _ default is valof{
      var (RToks,T0) is term00(Toks,Ops);
      valis termArgs(RToks,T0,Ops);
    }
  };

  parseInterpolation(Els,Lc,Ops) is let{
    parseEl(literalSegment(Str,SLc)) is asString(SLc,Str)
    parseEl(interpolateElement(Mode,Text,Fmt,SLc)) is valof{
      var (_,_,El) is term(stringTokens(Text,SLc),1199,Ops)
      if Mode = displayMode then
        valis asApply(SLc,asName(SLc,"format"),asTuple(SLc,"()",list of [El,asString(SLc,Fmt)]))
      else
        valis asApply(SLc,asName(SLc,"coerce"),asTuple(SLc,"()",list of [El,asString(SLc,Fmt)]))
    }
  } in leftFold1(fn(L,R)=>asApply(Lc,asName(Lc,"++"),asTuple(Lc,"()",list of [L,R])),map(parseEl,Els))

  term00(Tks,Ops) where nxtTok(Tks,Ops) matches (idTok(Id,Lc),Toks) is case Id in {
    "\#(" is valof{
      var (RToks,_,T) is term(Toks,2000,Ops);
      if nxtTok(RToks,Ops) matches (idTok(")\#",_),RToks2) then
        valis (RToks2,T)
      else{
        reportError("expecting a \")\#\", opening \"\#(\" at $Lc",list of [Lc,peekLoc(RToks,Ops)]);
        valis (RToks,T)
      }
    };
    "\(" is parseParens(Lc,Toks,1200,Ops);
    "\{" is parseBraces(Lc,Toks,Ops);
    Nm default is 
      isLeftBracket(Nm,Ops) matches some(BkSpec) ? parseBrackets(Lc,Toks,Ops,BkSpec) |
      (Toks,asName(Lc,Nm));
  };
  term00(Tks,Ops) where nxtTok(Tks,Ops) matches (Tk,Toks) is valof{
    reportError("expecting an identifier, not $Tk",list of {tokenLoc(Tk)});
    valis term00(Toks,Ops);
  };

  private peekLoc(Toks,Ops) where nxtTok(Toks,Ops) matches (Tk,_) is tokenLoc(Tk);

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

  parseParens(stLc,Tks,_,Ops) where nxtTok(Tks,Ops) matches (idTok("\)",xLc),Toks)  is 
      (Toks,tple(mergeLocation(stLc,xLc),list of []));
  parseParens(stLc,Tokens,Priority,Ops) is let{
    parseParen(Toks) is valof{
      var (TToks,_,T) is term(Toks,Priority,Ops);

      case nxtTok(TToks,Ops) in {
        (idTok(")",tlLc),RToks) do valis (RToks,tple(mergeLocation(stLc,tlLc),tupleize(T)));
        (HdTk,RToks) default do {
          reportError("expecting a closing paren, not $HdTk",list of [tokenLoc(HdTk)])
          valis (RToks,tple(mergeLocation(stLc,tokenLoc(HdTk)),tupleize(T)))        }
      }
    }

    tupleize(asApply(_,asName(_,","),asTuple(_,"()",list of [L,R]))) is list of [L,..tupleize(R)]
    tupleize(T) is list of [T]

  } in parseParen(Tokens)

  parseBraces(stLc,Toks,Ops) where nxtTok(Toks,Ops) matches (idTok("}",xLc),Tokens) is 
      (Tokens,asName(mergeLocation(stLc,xLc),"{}"));
  parseBraces(stLc,Tokens,Operators) is let{
    parseBrace(Toks,Els,Ops) is valof{
      var (RToks,_,T) is term(Toks,1999,Ops);
      var Ops1 is checkForOperators(T,Ops);

      case nxtTok(RToks,Ops1) in {
        (idTok("\}",tlLc),TToks) do valis (TToks,block(mergeLocation(stLc,tlLc),list of [Els..,T]));
        (idTok(";",_),TToks) do 
          if nxtTok(TToks,Ops1) matches (idTok("\}",tlLc),rstToks) then
            valis (rstToks,block(mergeLocation(stLc,tlLc),list of [Els..,T]))
          else
            valis parseBrace(TToks,list of [Els..,T],Ops1);
        (terminal,_) do valis (RToks,block(mergeLocation(stLc,locOf(T)),list of [Els..,T]))
        _ default do {
          valis parseBrace(RToks,list of [Els..,T],Ops1)
        }
      }
    }
  } in parseBrace(Tokens,list of [],Operators);


  parseBrackets(stLc,Tks,Ops,Bkt) where nxtTok(Tks,Ops) matches (idTok(Rgt,xLc),Toks) and Rgt=Bkt.right is
    (Toks,asTuple(mergeLocation(stLc,xLc),Bkt.op,list of []));
  parseBrackets(stLc,Tokens,Ops,Bkt) is let{
    var Rgt is Bkt.right;
    var Priority is Bkt.inPrior;

    parseBkt(Toks,Els) is valof{
      var (RToks,_,T) is term(Toks,Priority,Ops);

      case nxtTok(RToks,Ops) in {
        (idTok(R,tlLc),TToks) where R=Rgt do valis 
              (TToks,asTuple(mergeLocation(stLc,tlLc),Bkt.op,list of [Els..,T]));
        (idTok(",",_),TToks) do valis parseBkt(TToks,list of [Els..,T]);
        (HdTk,TToks) default do {
          reportError("expecting a ',' or '$Rgt', not $HdTk, '(' at $stLc",list of [tokenLoc(HdTk)]);
          valis parseBkt(TToks,list of [Els..,T])
        }
      }
    }
  } in parseBkt(Tokens,list of []);

  termArgs(Tokens,Lhs,Ops) where nxtTok(Tokens,Ops) matches (Tk,Tks) is case Tk in {
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

  collectStringTokens(SoFar,Lc,Tokens,Ops) where nxtTok(Tokens,Ops) matches (stringTok(Str,LcN),Toks) is 
    collectStringTokens(SoFar++Str,LcN,Toks,Ops);
  collectStringTokens(SoFar,Lc,Toks,_) default is (Toks,0,asString(Lc,SoFar));

  isRightBracketNext(Tokens,Ops) where nxtTok(Tokens,Ops) matches (idTok(N,_),_) is isRightBracket(N,Ops) matches some(_);
  isRightBracketNext(_,_) default is false;

  private showTokenState((Tk,St)) is valof{
    logMsg(info,"next token $Tk/$(St.currLine):$(St.currOff)")
    valis (Tk,St)
  }

  private nxtTok(St,Ops) is let{
    followMulti(cuSt,G) where nextToken(cuSt,Ops) matches (idTok(Id,_),cuS) and followTrie(Id,G) has value nextTrie is followMulti(cuS,nextTrie)
    followMulti(cuSt,G) where isTermTrie(G) is (idTok(trieVal(G),deltaLoc(St,cuSt)),cuSt)
    followMulti(cuSt,G) default is nextToken(cuSt,Ops)
  } in followMulti(St,Ops.multiops);
}


