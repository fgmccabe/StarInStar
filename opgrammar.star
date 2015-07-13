opgrammar is package{
  private import errors
  private import lexer
  private import operators
  private import trie
  private import leftRight
  private import ast

  fun term(Toks,priority,Ops) is termRight(termLeft(Toks,priority,Ops),priority,Ops)

  fun termLeft(Toks,priority,Ops) where nxtTok(Toks,Ops) matches (Tk,nToks) is 
    switch Tk in {
      case idTok(Name,Lc) is valof{
        if isPrefixOp(Name,Ops,priority) matches some(OpSpec) then {
          if OpSpec.priority<=priority then {
            def (RToks,_,Right) is term(nToks,OpSpec.right,Ops)
            valis (RToks,OpSpec.priority,
              oneApply(mergeLocation(Lc,locOf(Right)),asName(Lc,Name),Right))
          } else{
            reportError("prefix operator $Name of priority $(OpSpec.priority) not permitted here",list of [Lc])
            valis (nToks,0,asName(Lc,Name))
          }
        } else
          valis term0(Toks,Ops)
      }
      case T default is term0(Toks,Ops)
   }

  fun termRight((Toks,LeftPrior,Left),Prior,Ops) where nxtTok(Toks,Ops) matches (Hed,Rest) is 
    switch Hed in {
      case terminal is (Toks,0,Left)
      case idTok(Op,Lc) where isRightBracket(Op,Ops) matches some(_) is (Toks,LeftPrior,Left)
      case idTok(Op,Lc) where isInfixOp(Op,Ops,Prior) matches some(InfSpec) and 
            InfSpec.left>=LeftPrior and InfSpec.priority <= Prior is valof{
        if isPostfixOp(Op,Ops,Prior) matches some(Post) and 
          Post.left>=LeftPrior and Post.priority <= Prior then{
            var treatAsPostfix := false

            if nxtTok(Rest,Ops) matches (idTok(Nm,nLc),_) then{
              if isRightBracket(Nm,Ops) matches some(_) then{
                treatAsPostfix := true
              }
              else if isPrefixOp(Nm,Ops,Prior) matches some(PrOp) then {
                treatAsPostfix := PrOp.priority>=InfSpec.priority
              }
              else if isInfixOp(Nm,Ops,Prior) matches some(NxOp) then 
                treatAsPostfix := NxOp.priority>=InfSpec.priority
              }
              if treatAsPostfix then
                valis termRight((Rest,Post.priority,
                  oneApply(mergeLocation(locOf(Left),Lc),
                  asName(Lc,Op),Left)),Prior,Ops)
              else{
                def (RToks,_,R) is term(Rest,InfSpec.right,Ops)
                valis termRight((RToks,InfSpec.priority,
                 binApply(mergeLocation(locOf(Left),locOf(R)),
                  asName(Lc,Op),Left,R)),Prior,Ops)
              }
            }
            else{
              -- infix only
              def (RToks,_,R) is term(Rest,InfSpec.right,Ops)
              valis termRight((RToks,InfSpec.priority,
               binApply(mergeLocation(locOf(Left),locOf(R)),
                asName(Lc,Op),Left,R)),Prior,Ops)
            }
          }

        case idTok(Op,Lc) where isPostfixOp(Op,Ops,Prior) matches some(PostSpec) and 
            PostSpec.left>=LeftPrior and PostSpec.priority <=Prior is 
          termRight((Rest,PostSpec.priority,
             oneApply(mergeLocation(locOf(Left),Lc),
             asName(Lc,Op),Left)),Prior,Ops)

        case _ default is (Toks,LeftPrior,Left)
      }

  fun term0(Toks,Ops) where nxtTok(Toks,Ops) matches (Hed,Rest) is switch Hed in {
    case integerTok(Ix,Lc) is (Rest,0,asInteger(Lc,Ix))
    case longTok(Ix,Lc) is (Rest,0,asLong(Lc,Ix))
    case floatTok(Dx,Lc) is (Rest,0,asFloat(Lc,Dx))
    case decimalTok(Dx,Lc) is (Rest,0,asDecimal(Lc,Dx))
    case charTok(Ch,Lc) is (Rest,0,asChar(Lc,Ch))
    case stringTok(Str,Lc) is collectStringTokens(Str,Lc,Rest,Ops)
    case interpolatedString(Els,Lc) is (Rest,0,parseInterpolation(Els,Lc,Ops))
    case regexpTok(Str,Lc) is (Rest,0,unary(Lc,"*regexp*",asString(Lc,Str)))
    case _ default is valof{
      def (RToks,T0,lLc) is term00(Toks,Ops)
      valis termArgs(RToks,T0,Ops,lLc)
    }
  }

  fun parseInterpolation(Els,Lc,Ops) is let{
    fun parseEl(literalSegment(Str,SLc)) is asString(SLc,Str)
     |  parseEl(interpolateElement(Mode,Text,Fmt,SLc)) is valof{
          def (_,_,El) is term(stringTokens(Text,SLc),1199,Ops)
          if Mode = displayMode then
            valis asApply(SLc,asName(SLc,"format"),asTuple(SLc,"()",list of [El,asString(SLc,Fmt)]))
          else
            valis asApply(SLc,asName(SLc,"coerce"),asTuple(SLc,"()",list of [El,asString(SLc,Fmt)]))
        }
  } in leftFold1(fn(L,R)=>asApply(Lc,asName(Lc,"++"),asTuple(Lc,"()",list of [L,R])),map(parseEl,Els))

  fun term00(Tks,Ops) where nxtTok(Tks,Ops) matches (idTok(Id,Lc),Toks) is switch Id in {
        case "\#(" is valof{
          def (RToks,_,T) is term(Toks,2000,Ops)
          if nxtTok(RToks,Ops) matches (idTok(")\#",lLc),RToks2) then
            valis (RToks2,T,lLc)
          else{
            def lLc is peekLoc(RToks,Ops)
            reportError("expecting a \")\#\", opening \"\#(\" at $Lc",list of [Lc,lLc])
            valis (RToks,T,lLc)
          }
        };
        case "\(" is parseParens(Lc,Toks,Ops)
        case "\{" is parseBraces(Lc,Toks,Ops)
        case Nm default is 
          isLeftBracket(Nm,Ops) has value BkSpec ? 
              parseBrackets(Lc,Toks,Ops,BkSpec) : (Toks,asName(Lc,Nm),Lc)
      }
   |  term00(Tks,Ops) where nxtTok(Tks,Ops) matches (Tk,Toks) is valof{
        reportError("expecting an identifier, not $Tk",list of [tokenLoc(Tk)])
        valis term00(Toks,Ops)
      }

  private fun peekLoc(Toks,Ops) where nxtTok(Toks,Ops) matches (Tk,_) is tokenLoc(Tk)

  fun checkForOperators(T,Ops) where isUnary(T,"\#") matches some(Meta) is valof{
        if isTernary(Meta,"infix") has value (Lf,Md,Rt) then {
          if Lf matches asString(_,Op) then{
            if Md matches asInteger(_,Pr) then {
              if Rt matches asInteger(_,MinPrior) then
                valis defineInfix(Op,Pr-1,Pr,Pr-1,MinPrior,Ops)
              else
                reportError("expecting an integer, not $Rt",list of [locOf(Rt)])
            }
            else
              reportError("expecting an integer, not $Md",list of [locOf(Md)])
          }
          else
            reportError("expecting a operator name (string), not $Lf",list of [locOf(Lf)])
          valis Ops
        }
        else if isBinary(Meta,"infix") has value (L,R) then {
          if L matches asString(_,Op) then{
            if R matches asInteger(_,Pr) then
              valis defineInfix(Op,Pr-1,Pr,Pr-1,0,Ops)
            else
              reportError("expecting an integer, not $R",list of [locOf(R)])
          }
          else
            reportError("expecting a operator name (string), not $L",list of [locOf(L)])
          valis Ops
        }
        else if isTernary(Meta,"right") has value (Lf,Md,Rt) then {
          if Lf matches asString(_,Op) then{
            if Md matches asInteger(_,Pr) then {
              if Rt matches asInteger(_,MinPrior) then
                valis defineInfix(Op,Pr-1,Pr,Pr,MinPrior,Ops)
              else
                reportError("expecting an integer, not $Rt",list of [locOf(Rt)])
            }
            else
              reportError("expecting an integer, not $Md",list of [locOf(Md)])
          }
          else
            reportError("expecting a operator name (string), not $Lf",list of [locOf(Lf)])
          valis Ops
        }
        else if isBinary(Meta,"right") has value (L,R) then {
          if L matches asString(_,Op) then{
            if R matches asInteger(_,Pr) then
              valis defineInfix(Op,Pr-1,Pr,Pr,0,Ops)
            else
              reportError("expecting an integer, not $R",list of [locOf(R)])
          }
          else
            reportError("expecting a operator name (string), not $L",list of [locOf(L)])
          valis Ops
        }
        else if isTernary(Meta,"left") has value (Lf,Md,Rt) then {
          if Lf matches asString(_,Op) then{
            if Md matches asInteger(_,Pr) then {
              if Rt matches asInteger(_,MinPrior) then
                valis defineInfix(Op,Pr,Pr,Pr-1,MinPrior,Ops)
              else
                reportError("expecting an integer, not $Rt",list of [locOf(Rt)])
            }
            else
              reportError("expecting an integer, not $Md",list of [locOf(Md)])
          }
          else
            reportError("expecting a operator name (string), not $Lf",list of [locOf(Lf)])
          valis Ops
        }
        else if isBinary(Meta,"left") has value (L,R) then {
          if L matches asString(_,Op) then{
            if R matches asInteger(_,Pr) then
              valis defineInfix(Op,Pr,Pr,Pr-1,0,Ops)
            else
              reportError("expecting an integer, not $R",list of [locOf(R)])
          }
          else
            reportError("expecting a operator name (string), not $L",list of [locOf(L)])
          valis Ops
        }
        else if isTernary(Meta,"prefix") has value (Lf,Md,Rt) then {
          if Lf matches asString(_,Op) then{
            if Md matches asInteger(_,Pr) then {
              if Rt matches asInteger(_,MinPrior) then
                valis definePrefix(Op,Pr,Pr-1,MinPrior,Ops)
              else
                reportError("expecting an integer, not $Rt",list of [locOf(Rt)])
            }
            else
              reportError("expecting an integer, not $Md",list of [locOf(Md)])
          }
          else
            reportError("expecting a operator name (string), not $Lf",list of [locOf(Lf)])
          valis Ops
        }
        else if isBinary(Meta,"prefix") has value (L,R) then {
          if L matches asString(_,Op) then{
            if R matches asInteger(_,Pr) then
              valis definePrefix(Op,Pr,Pr-1,0,Ops)
            else
              reportError("expecting an integer, not $R",list of [locOf(R)])
          }
          else
            reportError("expecting a operator name (string), not $L",list of [locOf(L)])
          valis Ops
        }
        else if isBinary(Meta,"prefixAssoc") has value (L,R) then {
          if L matches asString(_,Op) then{
            if R matches asInteger(_,Pr) then
              valis definePrefix(Op,Pr,Pr,0,Ops)
            else
              reportError("expecting an integer, not $R",list of [locOf(R)])
          }
          else
            reportError("expecting a operator name (string), not $L",list of [locOf(L)])
          valis Ops
        }
        else if isTernary(Meta,"postfix") has value (Lf,Md,Rt) then {
          if Lf matches asString(_,Op) then{
            if Md matches asInteger(_,Pr) then {
              if Rt matches asInteger(_,MinPrior) then
                valis definePostfix(Op,Pr-1,Pr,MinPrior,Ops)
              else
                reportError("expecting an integer, not $Rt",list of [locOf(Rt)])
            }
            else
              reportError("expecting an integer, not $Md",list of [locOf(Md)])
          }
          else
            reportError("expecting a operator name (string), not $Lf",list of [locOf(Lf)])
          valis Ops
        }
        else if isBinary(Meta,"postfix") has value (L,R) then {
          if L matches asString(_,Op) then{
            if R matches asInteger(_,Pr) then
              valis definePrefix(Op,Pr-1,Pr,0,Ops)
            else
              reportError("expecting an integer, not $R",list of [locOf(R)])
          }
          else
            reportError("expecting a operator name (string), not $L",list of [locOf(L)])
          valis Ops
        }
        else if isBinary(Meta,"postfixAssoc") has value (L,R) then {
          if L matches asString(_,Op) then{
            if R matches asInteger(_,Pr) then
              valis definePostfix(Op,Pr,Pr,0,Ops)
            else
              reportError("expecting an integer, not $R",list of [locOf(R)])
          }
          else
            reportError("expecting a operator name (string), not $L",list of [locOf(L)])
          valis Ops
        }
        else if isUnary(Meta,"token") has value (T) then {
          if T matches asString(_,Op) then
            valis defineToken(Op,Ops)
          else
            reportError("expecting a operator name (string), not $T",list of [locOf(T)])
          valis Ops
        }
        else if isQuad(Meta,"pair") has value (L,M1,M2,R) then {
          if L matches asString(_,Lf) then {
            if M1 matches asString(_,Rt) then {
              if M2 matches asString(_,Op) then {
                if R matches asInteger(_,Pr) then {
                  valis defineBktPair(Lf,Rt,Lf++Rt,Op,Pr,Ops)
                } else
                  reportError("expecting a priority (integer), not $R",list of [locOf(R)])
              } else
                reportError("expecting a op name (string), not $M2",list of [locOf(M2)])
            } else
              reportError("expecting a right bracket name (string), not $M1",list of [locOf(M1)])
          } else
            reportError("expecting a left bracket name (string), not $L",list of [locOf(L)])
          valis Ops
        }
        else if isTernary(Meta,"pair") has value (L,M,R) then {
          if L matches asString(_,Lf) then {
            if M matches asString(_,Rt) then {
              if R matches asInteger(_,Pr) then {
                valis defineBktPair(Lf,Rt,Lf++Rt,"",Pr,Ops)
              } else
                reportError("expecting a priority (integer), not $R",list of [locOf(R)])
            } else
              reportError("expecting a right bracket name (string), not $M",list of [locOf(M)])
          } else
            reportError("expecting a left bracket name (string), not $L",list of [locOf(L)])
          valis Ops
        }
        else
          valis Ops
      }
   |  checkForOperators(T,Ops) default is Ops

  fun parseParens(stLc,Tks,Ops) where nxtTok(Tks,Ops) matches (idTok("\)",xLc),Toks)  is 
        (Toks,tple(mergeLocation(stLc,xLc),list of []),xLc)
   |  parseParens(stLc,Tokens,Ops) is let{
        fun parseParen(Toks) is valof{
          def (TToks,_,T) is term(Toks,1200,Ops)

          switch nxtTok(TToks,Ops) in {
            case (idTok(")",tlLc),RToks) do valis (RToks,tple(mergeLocation(stLc,tlLc),tupleize(T)),tlLc);
            case (HdTk,RToks) default do {
              def tlLc is tokenLoc(HdTk)
              reportError("expecting a closing paren, not $HdTk",list of [tlLc])
              valis (RToks,tple(mergeLocation(stLc,tokenLoc(HdTk)),tupleize(T)),tlLc)
            }
          }
        }

        fun tupleize(asApply(_,asName(_,","),asTuple(_,"()",list of [L,R]))) is list of [L,..tupleize(R)]
         |  tupleize(T) is list of [T]

      } in parseParen(Tokens)

  fun parseBraces(stLc,Toks,Ops) where nxtTok(Toks,Ops) matches (idTok("}",xLc),Tokens) is 
          (Tokens,asName(mergeLocation(stLc,xLc),"{}"),xLc)
   |  parseBraces(stLc,Tokens,Operators) is let{
        fun parseBrace(Toks,Els,Ops) is valof{
          def (RToks,_,T) is term(Toks,1999,Ops)
          def Ops1 is checkForOperators(T,Ops)

          switch nxtTok(RToks,Ops1) in {
            case (idTok("\}",tlLc),TToks) do valis (TToks,block(mergeLocation(stLc,tlLc),list of [Els..,T]),tlLc);
            case (idTok(";",_),TToks) do 
              if nxtTok(TToks,Ops1) matches (idTok("\}",tlLc),rstToks) then
                valis (rstToks,block(mergeLocation(stLc,tlLc),list of [Els..,T]),tlLc)
              else
                valis parseBrace(TToks,list of [Els..,T],Ops1);
            case (terminal,_) do valis (RToks,block(mergeLocation(stLc,locOf(T)),list of [Els..,T]),locOf(T))
            case _ default do {
              valis parseBrace(RToks,list of [Els..,T],Ops1)
            }
          }
        }
      } in parseBrace(Tokens,list of [],Operators)

  fun parseBrackets(stLc,Tks,Ops,Bkt) where nxtTok(Tks,Ops) matches (idTok(Rgt,xLc),Toks) and Rgt=Bkt.right is
        (Toks,asTuple(mergeLocation(stLc,xLc),Bkt.op,list of []),xLc)
   |  parseBrackets(stLc,Tokens,Ops,Bkt) is let{
        def Rgt is Bkt.right
        def Priority is Bkt.inPrior

        fun parseBkt(Toks,Els) is valof{
          def (RToks,_,T) is term(Toks,Priority,Ops)

          switch nxtTok(RToks,Ops) in {
            case (idTok(R,tlLc),TToks) where R=Rgt do valis 
                  (TToks,asTuple(mergeLocation(stLc,tlLc),Bkt.op,list of [Els..,T]),tlLc);
            case (idTok(",",_),TToks) do valis parseBkt(TToks,list of [Els..,T]);
            case (HdTk,TToks) default do {
              reportError("expecting a ',' or '$Rgt', not $HdTk, '(' at $stLc",list of [tokenLoc(HdTk)])
              valis parseBkt(TToks,list of [Els..,T])
            }
          }
        }
      } in parseBkt(Tokens,list of [])

  fun termArgs(Tokens,Lhs,Ops,lLc) where nxtTok(Tokens,Ops) matches (Tk,Tks) is switch Tk in {
    case idTok("(",Lc) where sameLine(Lc,lLc) is valof{ -- special handling needed for parens
      def (Toks,ArgsTuple,tlLc) is parseParens(Lc,Tks,Ops)
      valis termArgs(Toks,asApply(mergeLocation(locOf(Lhs),locOf(ArgsTuple)),
       Lhs,ArgsTuple),Ops,tlLc)
    }
    case idTok("{",Lc) where sameLine(Lc,lLc) is valof{ -- special handling needed for braces
      def (Toks,ArgsTuple,tlLc) is parseBraces(Lc,Tks,Ops)
      valis termArgs(Toks,asApply(mergeLocation(locOf(Lhs),locOf(ArgsTuple)),
       Lhs,ArgsTuple),Ops,tlLc)
    }
    case idTok(B,Lc) where sameLine(Lc,lLc) and isLeftBracket(B,Ops) matches some(BkSpec) is valof{
      def (Toks,ArgsTuple,tlLc) is parseBrackets(Lc,Tks,Ops,BkSpec)
      valis termArgs(Toks,asApply(mergeLocation(locOf(Lhs),locOf(ArgsTuple)),
       Lhs,ArgsTuple),Ops,tlLc)
    }
    case _ default is (Tokens,0,Lhs)
  }

  fun collectStringTokens(SoFar,Lc,Tokens,Ops) where nxtTok(Tokens,Ops) matches (stringTok(Str,LcN),Toks) is 
        collectStringTokens(SoFar++Str,LcN,Toks,Ops)
   |  collectStringTokens(SoFar,Lc,Toks,_) default is (Toks,0,asString(Lc,SoFar))

  fun isRightBracketNext(Tokens,Ops) where nxtTok(Tokens,Ops) matches (idTok(N,_),_) is isRightBracket(N,Ops) matches some(_)
   |  isRightBracketNext(_,_) default is false

  private fun showTokenState((Tk,St)) is valof{
    logMsg(info,"next token $Tk/$(St.currLine):$(St.currOff)")
    valis (Tk,St)
  }

  private fun nxtTok(St,Ops) is let{
    fun followMulti(cuSt,G) where nextToken(cuSt,Ops) matches (idTok(Id,_),cuS) and followTrie(Id,G) has value nextTrie is
          followMulti(cuS,nextTrie)
     |  followMulti(cuSt,G) where isTermTrie(G) is (idTok(trieVal(G),deltaLoc(St,cuSt)),cuSt)
     |  followMulti(cuSt,G) default is nextToken(cuSt,Ops)
  } in followMulti(St,Ops.multiops)
}
