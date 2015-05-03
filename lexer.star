lexer is package{
  private import location;
  private import errors;
  private import operators;
  private import stream;

  type token is idTok(string,srcLoc)
  or integerTok(integer,srcLoc)
    or longTok(long,srcLoc)
    or floatTok(float,srcLoc)
    or decimalTok(decimal,srcLoc)
    or charTok(char,srcLoc)
    or stringTok(string,srcLoc)
    or regexpTok(string,srcLoc)
    or interpolatedString(list of interpolationElement,srcLoc)
    or terminal;

  type interpolationElement is interpolateElement(interpolationMode,string,string,srcLoc) or literalSegment(string,srcLoc)

  type interpolationMode is displayMode or convertMode

  type tokenState is tokenState{
    text has type list of char;
    currLine has type integer;
    currOff has type integer;
    currPos has type integer;
  }

  private
  hedChar(tokenState{text=[Ch,.._]}) is some(Ch);
  hedChar(_) default is none;

  private hedHedChar(tokenState{text=[_,Ch,.._]}) is some(Ch);
  private hedHedHedChar(tokenState{text=[_,_,Ch,.._]}) is Ch;

  private 
  nxSt(tokenState{text=[Ch,..T];currLine=cuL;currOff=O;currPos=P}) is
    Ch='\n'?
      tokenState{text=T;currLine=cuL+1;currOff=0;currPos=P+1} |
      tokenState{text=T;currLine=cuL;currOff=O+1;currPos=P+1}
  nxSt(St matching tokenState{text=[]}) is St

  private mvSt(tokenState{text=T;currLine=cuL;currOff=O;currPos=P},off) is
    tokenState{text=T[off:];currLine=cuL;currOff=O+off;currPos=P+off};

  private isTerminal(tokenState{text=T}) is T=[];

  private isSpace(' ') is true;
  isSpace('\t') is true;
  isSpace(_) default is false;

  nextToken(tkSt,Ops) is let{

    skipToNxTok(St) where hedChar(St) has value hCh is
      case hCh in {
        ' ' is skipToNxTok(nxSt(St));
        '\t' is skipToNxTok(nxSt(St));
        '\n' is skipToNxTok(nxSt(St));
        '-' where hedHedChar(St) has value '-' and isSpace(hedHedHedChar(St)) is
          lineComment(St)
        '/' where hedHedChar(St) has value '*' is
          blockComment(mvSt(St,2));
        _ default is nxTok(St)
      }
    skipToNxTok(St) default is nxTok(St)

    lineComment(St) where hedChar(St) has value hCh is
      case hCh in {
        '\n' is skipToNxTok(nxSt(St));
        _ default is lineComment(nxSt(St))
      }
    lineComment(St) default is nxTok(St)

    blockComment(St) where hedChar(St) has value hCh is
      case hCh in {
        '*' is case hedHedChar(St) in {
          some('/') is skipToNxTok(nxSt(nxSt(St)))
          _ default is blockComment(nxSt(St))
        }
        _ default is blockComment(nxSt(St))
	  }
    blockComment(St) default is nxTok(St)

    nxTok(St) where hedChar(St) has value hCh is
      case hCh in {
        '.' where hedHedChar(St) has value nDCh and isDigit(nDCh) is readNumber(St);
        '\'' is case hedHedChar(St) in {
          some('s') is hedHedHedChar(St)='\''?
            report(charTok('s',locOf(St,3)),mvSt(St,3)) |
            report(idTok("'s",locOf(St,2)),mvSt(St,2))
          some('n') is hedHedHedChar(St)='\''?
            report(charTok('n',locOf(St,3)),mvSt(St,3)) |
            report(idTok("'n",locOf(St,2)),mvSt(St,2))
          _ default is readChar(nxSt(St),
              fn(cuSt,Ch)=>valof{
                if not hedChar(cuSt) has value '\'' then
                  reportError("expecting a ', got $(hedChar(cuSt))",list of [locOf(St,1)]);
                valis report(charTok(Ch,deltaLoc(St,nxSt(cuSt))),nxSt(cuSt))
              })
          }
        '\"' where hedHedChar(St) has value '\"' and hedHedHedChar(St)='\"' is
          readTripleQuoted(St);
        '\"' is readString(St);
        '\`' is readRegexp(St);
        '0' where hedHedChar(St) has value 'c' is
            readChar(mvSt(St,2),
              fn(nSt,ch)=>report(integerTok(ch as integer,deltaLoc(St,nSt)),nSt));
        '\\' is readIden(St,fn(Id,ISt)=>report(idTok(Id,deltaLoc(St,ISt)),ISt));
        D where isDigit(D) is readNumber(St);
        X where isLeadInChar(X) is let{
          -- follow the token graph
          followGraph(cuSt,soFar,Last,M) where hedChar(cuSt) has value Ch and isValidNextChar(Ch,M) is
            followGraph(nxSt(cuSt),cons of [Ch,..soFar],isTermGraph(M)?(soFar,cuSt)|Last,nextCharMap(Ch,M))

          followGraph(cuSt,soFar,_,M) where isTermGraph(M) is
            report(idTok(revImplode(soFar),deltaLoc(St,cuSt)),cuSt);

          followGraph(_,_,(last,lastSt),_) default is
            report(idTok(revImplode(last),deltaLoc(St,lastSt)),lastSt);
          var FG is someValue(firstGraph(X));
        } in followGraph(nxSt(St),cons of [X],isTermGraph(FG)?(cons of [X],St)|(cons of [],St),FG)

        Ch where isIdentifierStart(Ch) is readIden(St,fn(Id,ISt)=>report(idTok(Id,deltaLoc(St,ISt)),ISt));
        X default is valof{
          reportError("invalid char: $X/0x$(X as integer):XXXX;)",list of [locOf(St,1)]);
          valis nxTok(nxSt(St))
        }
      };
    nxTok(St) default is (terminal,St)

    readNumber(State) is let{
      readNum(St) where hedChar(St) has value hCh is case hCh in {
        '0' where hedHedChar(St) has value 'x' is readHex(mvSt(St,2),cons of []);
        _ default is readDigits(St,cons of [],readMoreNum)
      }

      readHex(St,soFar) where hedChar(St) has value D and isHexDigit(D) is readHex(nxSt(St),cons of [D,..soFar])
      readHex(St,soFar) where hedChar(St) has value 'l' or hedChar(St) has value 'L' is
        report(longTok(hex2long(revImplode(soFar)),deltaLoc(State,nxSt(St))),nxSt(St))
      readHex(St,soFar) default is
        report(integerTok(hex2integer(revImplode(soFar)),deltaLoc(State,St)),St)

      readDigits(St,soFar,Cont) where hedChar(St) has value D and isDigit(D) is readDigits(nxSt(St),cons of [D,..soFar],Cont)
      readDigits(St,soFar,Cont) is Cont(St,soFar);

      readMoreNum(St,soFar) where hedChar(St) has value '.' is readDigits(nxSt(St),cons of ['.',..soFar],readExponent)
      readMoreNum(St,soFar) where hedChar(St) has value 'l' or hedChar(St) has value 'L' is
        report(longTok(revImplode(soFar) as long,deltaLoc(State,St)),nxSt(St))
      readMoreNum(St,soFar) default is
        report(integerTok(revImplode(soFar) as integer,deltaLoc(State,St)),St)

      readExponent(St,soFar) where hedChar(St) has value 'e' and hedHedChar(St) has value '-' is
        readDigits(mvSt(St,2),cons of ['-','e',..soFar],mkFloat);
      readExponent(St,soFar) where hedChar(St) has value 'e' is
        readDigits(nxSt(St),cons of ['e',..soFar],mkFloat);
      readExponent(St,soFar) where hedChar(St) has value 'a' is
        report(decimalTok(revImplode(soFar) as decimal,deltaLoc(State,St)),nxSt(St))
      readExponent(St,soFar) default is mkFloat(St,soFar)

      mkFloat(St,soFar) is report(floatTok(revImplode(soFar) as float,deltaLoc(State,St)),St)
    } in readNum(State);

    readIden(State,Cont) is let{
      readId() where hedChar(State) has value F and isIdentifierStart(F) is readMore(nxSt(State),cons(F,nil));
      readId() where hedChar(State) has value '\\' is
        grabQtChar(nxSt(State),fn(cuSt,Ch) => readMore(cuSt,cons of [Ch]))

      readMore(St,Id) where hedChar(St) has value C and isIdentifierChar(C) is
          readMore(nxSt(St),cons of [C,..Id]);
      readMore(St,Id) where hedChar(St) has value '\\' is
          grabQtChar(nxSt(St),fn(cuSt,Ch) => readMore(cuSt,cons of [Ch,..Id]))
      readMore(St,Id) default is Cont(revImplode(Id),St);
    } in readId();

    readTripleQuoted(State) is let{
      readQuoted(St,soFar) where hedChar(St) has value '\"' and hedHedChar(St) has value '\"' and hedHedHedChar(St)='\"' is
        report(stringTok(revImplode(soFar),deltaLoc(State,mvSt(St,3))),mvSt(St,3))
      readQuoted(St,soFar) where hedChar(St) has value hCh is readQuoted(nxSt(St),cons of [hCh,..soFar]);
      readQuoted(St,soFar) where hedChar(St) = none is
        report(stringTok(revImplode(soFar),deltaLoc(State,St)),St)
    } in readQuoted(mvSt(State,3),cons of [])

    readChar(St,Cont) where hedChar(St) has value '\\' is
      grabQtChar(nxSt(St),Cont)
    readChar(St,Cont) where hedChar(St) has value '\n' is valof{
      reportError("unexpected newline",list of [locOf(St,1)]);
      valis report(charTok('\n',locOf(St,1)),nxSt(St))
    }
    readChar(St,Cont) where hedChar(St) has value hCh is Cont(nxSt(St),hCh)

    readRegexp(State) is let{
      readReg(St,soFar) where hedChar(St) has value '\`' is
        report(regexpTok(revImplode(soFar),deltaLoc(State,St)),nxSt(St));
      readReg(St,soFar) where hedChar(St) has value '\\' is
        grabQtChar(St,fn(cuSt,Ch)=>readReg(cuSt,cons of [Ch,..soFar]))
      readReg(St,soFar) where hedChar(St) has value nCh is readReg(nxSt(St),cons of [nCh,..soFar])
    } in readReg(nxSt(State),cons of []);

    grabQtChar(St,Cont) where hedChar(St) has value Ch is case Ch in {
      'b' is Cont(nxSt(St),'\b');
      'd' is Cont(nxSt(St),'\d');
      'e' is Cont(nxSt(St),'\e');
      'f' is Cont(nxSt(St),'\f');
      'n' is Cont(nxSt(St),'\n');
      'r' is Cont(nxSt(St),'\r');
      't' is Cont(nxSt(St),'\t');
      '\"' is Cont(nxSt(St),'\"');
      '\'' is Cont(nxSt(St),'\'');
      'u' is grabHex(nxSt(St),0,Cont);
      X default is Cont(nxSt(St),X);
    }

    grabHex(St,soFar,Cont) where hedChar(St) has value ';' is
      Cont(nxSt(St),soFar as char);
    grabHex(St,soFar,Cont) where hedChar(St) has value X and isHexDigit(X) is
      grabHex(nxSt(St),soFar*16+hexDigitVal(X),Cont)
    grabHex(St,soFar,Cont) is
      Cont(St,soFar as char);

    readString(State) is let{
      readStr(St,soFar) where hedChar(St) has value X is case X in {
        '\\' is grabQtChar(nxSt(St),fn(cuSt,Ch)=>readStr(cuSt,cons of [Ch,..soFar]))
        '\"' is report(stringTok(revImplode(soFar),deltaLoc(State,St)),nxSt(St))
        '$' is interpolate(nxSt(St),list of [literalSegment(revImplode(soFar),deltaLoc(State,St))],displayMode)
        '#' is interpolate(nxSt(St),list of [literalSegment(revImplode(soFar),deltaLoc(State,St))],convertMode)
        Ch default is readStr(nxSt(St),cons of [Ch,..soFar])
      }

      interpolate(St,soFar,Mode) where hedChar(St) has value Ch is case Ch in {
        '\(' is bracketCont(St,fn(Text,ESt)=>
            readFormat(ESt,fn(Fmt,FSt)=>interpolateMore(FSt,list of [soFar..,interpolateElement(Mode,Text,Fmt,deltaLoc(St,FSt))])))
        X where isIdentifierChar(X) is
          readIden(St,fn(Id,ESt)=>
            readFormat(ESt,fn(Fmt,FSt)=>interpolateMore(FSt,list of [soFar..,interpolateElement(Mode,Id,Fmt,deltaLoc(St,FSt))])))
      }

      readFormat(St,Cont) where hedChar(St) has value ':' is let{
        readFmt(cuSt,soFar) where hedChar(cuSt) has value hCh is case hCh in {
          ':' is Cont(revImplode(soFar),nxSt(cuSt));
          Ch default is readFmt(nxSt(cuSt),cons of [Ch,..soFar])
        }
        readFmt(cuSt,soFar) default is Cont(revImplode(soFar),cuSt);
      } in readFmt(nxSt(St),cons of []);
      readFormat(St,Cont) default is Cont("",St)

      bracketCont(Stte,Cont) is let{
        bktCont(St,soFar,[Exp]) where hedChar(St) has value Exp is
          Cont(revImplode(cons of [Exp,..soFar]),nxSt(St))
        bktCont(St,soFar,[Exp,..ting]) where hedChar(St) has value Exp is
          bktCont(nxSt(St),cons of [Exp,..soFar],ting)
        bktCont(St,soFar,Exp) where hedChar(St) has value hCh is case hCh in {
          '\(' is bktCont(nxSt(St),cons of ['\(',..soFar],cons of ['\)',..Exp])
          '\[' is bktCont(nxSt(St),cons of ['\[',..soFar],cons of ['\]',..Exp])
          '\{' is bktCont(nxSt(St),cons of ['\{',..soFar],cons of ['\}',..Exp])
          Ch default is bktCont(nxSt(St),cons of [Ch,..soFar],Exp)
        }
      } in bktCont(Stte,cons of [],cons of [])

      interpolateMore(SSt,segments) is let{
        stringSeg(St,soFar) where hedChar(St) has value hCh is case hCh in {
          '\\' is grabQtChar(nxSt(St),fn(cuSt,Ch)=>stringSeg(cuSt,cons of [Ch,..soFar]))
          '\"' is report(interpolatedString(list of [segments..,literalSegment(revImplode(soFar),deltaLoc(SSt,St))],deltaLoc(State,St)),nxSt(St))
          '$' is interpolate(nxSt(St),list of [segments..,literalSegment(revImplode(soFar),deltaLoc(SSt,St))],displayMode)
          '#' is interpolate(nxSt(St),list of [segments..,literalSegment(revImplode(soFar),deltaLoc(SSt,St))],convertMode)
          Ch default is stringSeg(nxSt(St),cons of [Ch,..soFar])
        }
      } in stringSeg(SSt,cons of []);
    } in readStr(nxSt(State),cons of []);

    report(Tk,St) is (Tk,St)
  } in skipToNxTok(tkSt)

  -- These function pick up the standard java notion of identifier
  isIdentifierStart(char(C)) is __isIdentifierStart(C);
  isIdentifierChar(char(C)) is __isIdentifierPart(C);

  private isHexDigit(X) is ('0'<=X and X<='9') or ('a'<=X and X<='f') or ('A'<=X and X<='F');
  private
  isDigit('0') is true;
  isDigit('1') is true;
  isDigit('2') is true;
  isDigit('3') is true;
  isDigit('4') is true;
  isDigit('5') is true;
  isDigit('6') is true;
  isDigit('7') is true;
  isDigit('8') is true;
  isDigit('9') is true;
  isDigit(_) default is false;

  hexDigitVal(X) where '0'<=X and X<='9' is X as integer-'0' as integer;
  hexDigitVal(X) where 'a'<=X and X<='f' is X as integer-'a' as integer+10;
  hexDigitVal(X) where 'A'<=X and X<='F' is X as integer-'A' as integer+10;

  revImplode has type (cons of char)=>string;
  private revImplode(X) is string(__string_rev_implode(X));

  implementation pPrint over token is {
    ppDisp(Tok) is shTok(Tok);
  } using {
    shTok(idTok(idnt,Lc)) is ppSequence(0,cons of [ppStr("["), ppStr(idnt), ppStr("]")]);
    shTok(integerTok(Ix,Lc)) is ppSequence(0,cons of [ppStr(Ix as string)]);
    shTok(longTok(Lx,Lc)) is ppSequence(0,cons of [ppStr(Lx as string),ppStr("l")]);
    shTok(floatTok(Dx,Lc)) is ppSequence(0,cons of [ppStr(Dx as string)]);
    shTok(decimalTok(Dx,Lc)) is ppSequence(0,cons of [ppStr(Dx as string),ppStr("a")]);
    shTok(charTok(Cx,Lc)) is ppDisp(Cx);
    shTok(stringTok(Sx,Lc)) is ppDisp(Sx);
    shTok(regexpTok(Sx,Lc)) is ppSequence(0,cons of [ppStr("\`"), ppStr(Sx), ppStr("\`")]);
    shTok(interpolatedString(L,_)) is ppSequence(0,cons of [ppStr("\""), ppContents(L), ppStr("\"")]);
    shTok(terminal) is ppStr("terminal");

    ppContents(L) is ppSequence(0,cons of {all ppEl(C) where C in L})

    ppEl(interpolateElement(displayMode,T,"",_)) is ppSequence(0,cons of [ppStr("\$"),ppStr(T),ppStr(";")]);
    ppEl(interpolateElement(displayMode,T,F,_)) is ppSequence(0,cons of [ppStr("\$"),ppStr(T),ppStr(":"),ppStr(F),ppStr(";")]);
    ppEl(interpolateElement(convertMode,T,"",_)) is ppSequence(0,cons of [ppStr("\#"),ppStr(T),ppStr(";")]);
    ppEl(interpolateElement(convertMode,T,F,_)) is ppSequence(0,cons of [ppStr("\#"),ppStr(T),ppStr(":"),ppStr(F),ppStr(";")]);
    ppEl(literalSegment(T,_)) is ppStr(T);

    showLc(Lc) is ppDisp(Lc);
  }

  tokenLoc(idTok(_,Lc)) is Lc;
  tokenLoc(integerTok(_,Lc)) is Lc;
  tokenLoc(longTok(_,Lc)) is Lc;
  tokenLoc(floatTok(_,Lc)) is Lc;
  tokenLoc(decimalTok(_,Lc)) is Lc;
  tokenLoc(charTok(_,Lc)) is Lc;
  tokenLoc(stringTok(_,Lc)) is Lc;
  tokenLoc(regexpTok(_,Lc)) is Lc;
  tokenLoc(interpolatedString(_,Lc)) is Lc;
  tokenLoc(terminal) is missing;

  locOf(tokenState{currLine=L; currOff=F; currPos=P},Ln) is
    someWhere{lineCount=L;lineOffset=F;charCount=P;length=Ln}

  deltaLoc(tokenState{currLine=L; currOff=F; currPos=P},tokenState{currPos=PE}) is 
    someWhere{lineCount=L;lineOffset=F;charCount=P;length=PE-P}

  revImplode(L) is implode(reverse(L));

  -- Handle stream of tokens
  loadUri has type (uri)=>string;
  loadUri(U) is string(__getUri(U));

  tokenize(U) is tokenState{
    text=explode(loadUri(U as uri));
    currLine = 1;
    currOff = 0;
    currPos = 0;
  }

  stringTokens(S,Lc) is tokenState{
    text = explode(S)
    currLine = Lc.lineCount
    currOff = Lc.lineOffset
    currPos = 0
  }
}