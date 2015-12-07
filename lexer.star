lexer is package{
  private import location
  private import errors
  private import operators
  private import stream

  type token is idTok(string,srcLoc)
    or integerTok(integer,srcLoc)
    or longTok(long,srcLoc)
    or floatTok(float,srcLoc)
    or decimalTok(decimal,srcLoc)
    or charTok(char,srcLoc)
    or stringTok(string,srcLoc)
    or regexpTok(string,srcLoc)
    or interpolatedString(list of interpolationElement,srcLoc)
    or terminal

  implementation hasLocation over token is {
    fun locOf(idTok(_,Lc)) is Lc
     |  locOf(integerTok(_,Lc)) is Lc
     |  locOf(longTok(_,Lc)) is Lc
     |  locOf(floatTok(_,Lc)) is Lc
     |  locOf(decimalTok(_,Lc)) is Lc
     |  locOf(charTok(_,Lc)) is Lc
     |  locOf(stringTok(_,Lc)) is Lc
     |  locOf(regexpTok(_,Lc)) is Lc
     |  locOf(interpolatedString(_,Lc)) is Lc
     |  locOf(terminal) is missing
  }

  type interpolationElement is interpolateElement(interpolationMode,string,string,srcLoc) or literalSegment(string,srcLoc)

  type interpolationMode is displayMode or convertMode

  type tokenState is tokenState{
    text has type list of char
    currLine has type integer
    currOff has type integer
    currPos has type integer
  }

  private
  fun hedChar(tokenState{text=[Ch,.._]}) is some(Ch)
   |  hedChar(_) default is none

  private fun hedHedChar(tokenState{text=[_,Ch,.._]}) is some(Ch)
  private fun hedHedHedChar(tokenState{text=[_,_,Ch,.._]}) is Ch

  private 
  fun nxSt(tokenState{text=[Ch,..T];currLine=cuL;currOff=O;currPos=P}) is
        Ch='\n'?
          tokenState{text=T;currLine=cuL+1;currOff=0;currPos=P+1} :
          tokenState{text=T;currLine=cuL;currOff=O+1;currPos=P+1}
   |  nxSt(St matching tokenState{text=[]}) is St

  private fun mvSt(tokenState{text=T;currLine=cuL;currOff=O;currPos=P},off) is
    tokenState{text=T[off:];currLine=cuL;currOff=O+off;currPos=P+off}

  private fun isTerminal(tokenState{text=T}) is T=[]

  private
  fun isSpace(' ') is true
   |  isSpace('\t') is true
   |  isSpace(_) default is false

  fun nextToken(tkSt,Ops) is let{

    fun skipToNxTok(St) where hedChar(St) has value hCh is
          switch hCh in {
            case ' ' is skipToNxTok(nxSt(St))
            case '\t' is skipToNxTok(nxSt(St))
            case '\n' is skipToNxTok(nxSt(St))
            case '-' where hedHedChar(St) has value '-' and isSpace(hedHedHedChar(St)) is
                  lineComment(St)
            case '/' where hedHedChar(St) has value '*' is
                  blockComment(mvSt(St,2))
            case _ default is nxTok(St)
          }
     |  skipToNxTok(St) default is nxTok(St)

    fun lineComment(St) where hedChar(St) has value hCh is
          switch hCh in {
            case '\n' is skipToNxTok(nxSt(St))
            case _ default is lineComment(nxSt(St))
          }
     |  lineComment(St) default is nxTok(St)

    fun blockComment(St) where hedChar(St) has value hCh is
          switch hCh in {
            case '*' is switch hedHedChar(St) in {
              case some('/') is skipToNxTok(nxSt(nxSt(St)))
              case _ default is blockComment(nxSt(St))
            }
            case _ default is blockComment(nxSt(St))
    	  }
     |  blockComment(St) default is nxTok(St)

    fun nxTok(St) where hedChar(St) has value hCh is
          switch hCh in {
            case '.' where hedHedChar(St) has value nDCh and isDigit(nDCh) is readNumber(St)
            case '\'' is switch hedHedChar(St) in {
              case some('s') is hedHedHedChar(St)='\''?
                report(charTok('s',tkLoc(St,3)),mvSt(St,3)) :
                report(idTok("'s",tkLoc(St,2)),mvSt(St,2))
              case some('n') is hedHedHedChar(St)='\''?
                report(charTok('n',tkLoc(St,3)),mvSt(St,3)) :
                report(idTok("'n",tkLoc(St,2)),mvSt(St,2))
              case _ default is readChar(nxSt(St),
                  fn(cuSt,Ch)=>valof{
                    if not hedChar(cuSt) has value '\'' then
                      reportError("expecting a ', got $(hedChar(cuSt))",list of [tkLoc(St,1)])
                    valis report(charTok(Ch,deltaLoc(St,nxSt(cuSt))),nxSt(cuSt))
                  })
              }
            case '\"' where hedHedChar(St) has value '\"' and hedHedHedChar(St)='\"' is
              readTripleQuoted(St)
            case '\"' is readString(St)
            case '\`' is readRegexp(St)
            case '0' where hedHedChar(St) has value 'c' is
                readChar(mvSt(St,2),
                  fn(nSt,ch)=>report(integerTok(ch as integer,deltaLoc(St,nSt)),nSt))
            case '\\' is readIden(St,fn(Id,ISt)=>report(idTok(Id,deltaLoc(St,ISt)),ISt))
            case D where isDigit(D) is readNumber(St)
            case X where isLeadInChar(X) is let{
                -- follow the token graph
                fun followGraph(cuSt,soFar,Last,M) where hedChar(cuSt) has value Ch and isValidNextChar(Ch,M) is
                      followGraph(nxSt(cuSt),cons of [Ch,..soFar],isTermGraph(M)?(soFar,cuSt):Last,nextCharMap(Ch,M))
                 |  followGraph(cuSt,soFar,_,M) where isTermGraph(M) is
                      report(idTok(revImplode(soFar),deltaLoc(St,cuSt)),cuSt)
                 |  followGraph(_,_,(last,lastSt),_) default is
                      report(idTok(revImplode(last),deltaLoc(St,lastSt)),lastSt)
                def FG is someValue(firstGraph(X))
              } in followGraph(nxSt(St),cons of [X],isTermGraph(FG)?(cons of [X],St):(cons of [],St),FG)
            case Ch where isIdentifierStart(Ch) is readIden(St,fn(Id,ISt)=>report(idTok(Id,deltaLoc(St,ISt)),ISt))
            case X default is valof{
              reportError("invalid char: $X/0x$(X as integer):XXXX;)",list of [tkLoc(St,1)])
              valis nxTok(nxSt(St))
            }
          }
     |  nxTok(St) default is (terminal,St)

    fun readNumber(State) is let{
      fun readNum(St) where hedChar(St) has value hCh is switch hCh in {
          case '0' where hedHedChar(St) has value 'x' is readHex(mvSt(St,2),cons of [])
          case _ default is readDigits(St,cons of [],readMoreNum)
        }

      fun readHex(St,soFar) where hedChar(St) has value D and isHexDigit(D) is readHex(nxSt(St),cons of [D,..soFar])
       |  readHex(St,soFar) where hedChar(St) has value 'l' or hedChar(St) has value 'L' is
            report(longTok(hex2long(revImplode(soFar)),deltaLoc(State,nxSt(St))),nxSt(St))
       |  readHex(St,soFar) default is
            report(integerTok(hex2integer(revImplode(soFar)),deltaLoc(State,St)),St)

      fun readDigits(St,soFar,Cont) where hedChar(St) has value D and isDigit(D) is readDigits(nxSt(St),cons of [D,..soFar],Cont)
       |  readDigits(St,soFar,Cont) is Cont(St,soFar)

      fun readMoreNum(St,soFar) where hedChar(St) has value '.' is readDigits(nxSt(St),cons of ['.',..soFar],readExponent)
       |  readMoreNum(St,soFar) where hedChar(St) has value 'l' or hedChar(St) has value 'L' is
            report(longTok(revImplode(soFar) as long,deltaLoc(State,St)),nxSt(St))
       |  readMoreNum(St,soFar) default is
            report(integerTok(revImplode(soFar) as integer,deltaLoc(State,St)),St)

      fun readExponent(St,soFar) where hedChar(St) has value 'e' and hedHedChar(St) has value '-' is
            readDigits(mvSt(St,2),cons of ['-','e',..soFar],mkFloat)
       |  readExponent(St,soFar) where hedChar(St) has value 'e' is
            readDigits(nxSt(St),cons of ['e',..soFar],mkFloat)
       |  readExponent(St,soFar) where hedChar(St) has value 'a' is
            report(decimalTok(revImplode(soFar) as decimal,deltaLoc(State,St)),nxSt(St))
       |  readExponent(St,soFar) default is mkFloat(St,soFar)

      fun mkFloat(St,soFar) is report(floatTok(revImplode(soFar) as float,deltaLoc(State,St)),St)
    } in readNum(State)

    fun readIden(State,Cont) is let{
      fun readId() where hedChar(State) has value F and isIdentifierStart(F) is readMore(nxSt(State),cons(F,nil))
       |  readId() where hedChar(State) has value '\\' is
            grabQtChar(nxSt(State),fn(cuSt,Ch) => readMore(cuSt,cons of [Ch]))

      fun readMore(St,Id) where hedChar(St) has value C and isIdentifierChar(C) is
            readMore(nxSt(St),cons of [C,..Id])
       |  readMore(St,Id) where hedChar(St) has value '\\' is
            grabQtChar(nxSt(St),fn(cuSt,Ch) => readMore(cuSt,cons of [Ch,..Id]))
       |  readMore(St,Id) default is Cont(revImplode(Id),St)
    } in readId()

    fun readTripleQuoted(State) is let{
      fun readQuoted(St,soFar) where hedChar(St) has value '\"' and hedHedChar(St) has value '\"' and hedHedHedChar(St)='\"' is
            report(stringTok(revImplode(soFar),deltaLoc(State,mvSt(St,3))),mvSt(St,3))
       |  readQuoted(St,soFar) where hedChar(St) has value hCh is readQuoted(nxSt(St),cons of [hCh,..soFar])
       |  readQuoted(St,soFar) where hedChar(St) = none is
            report(stringTok(revImplode(soFar),deltaLoc(State,St)),St)
    } in readQuoted(mvSt(State,3),cons of [])

    fun readChar(St,Cont) where hedChar(St) has value '\\' is
          grabQtChar(nxSt(St),Cont)
     |  readChar(St,Cont) where hedChar(St) has value '\n' is valof{
          reportError("unexpected newline",list of [tkLoc(St,1)])
          valis report(charTok('\n',tkLoc(St,1)),nxSt(St))
        }
     |  readChar(St,Cont) where hedChar(St) has value hCh is Cont(nxSt(St),hCh)

    fun readRegexp(State) is let{
      fun readReg(St,soFar) where hedChar(St) has value '\`' is
            report(regexpTok(revImplode(soFar),deltaLoc(State,St)),nxSt(St))
       |  readReg(St,soFar) where hedChar(St) has value '\\' is
            grabQtChar(St,fn(cuSt,Ch)=>readReg(cuSt,cons of [Ch,..soFar]))
       |  readReg(St,soFar) where hedChar(St) has value nCh is readReg(nxSt(St),cons of [nCh,..soFar])
    } in readReg(nxSt(State),cons of [])

    fun grabQtChar(St,Cont) where hedChar(St) has value Ch is switch Ch in {
      case 'b' is Cont(nxSt(St),'\b')
      case 'd' is Cont(nxSt(St),'\d')
      case 'e' is Cont(nxSt(St),'\e')
      case 'f' is Cont(nxSt(St),'\f')
      case 'n' is Cont(nxSt(St),'\n')
      case 'r' is Cont(nxSt(St),'\r')
      case 't' is Cont(nxSt(St),'\t')
      case '\"' is Cont(nxSt(St),'\"')
      case '\'' is Cont(nxSt(St),'\'')
      case 'u' is grabHex(nxSt(St),0,Cont)
      case X default is Cont(nxSt(St),X)
    }

    fun grabHex(St,soFar,Cont) where hedChar(St) has value ';' is
          Cont(nxSt(St),soFar as char)
     |  grabHex(St,soFar,Cont) where hedChar(St) has value X and isHexDigit(X) is
          grabHex(nxSt(St),soFar*16+hexDigitVal(X),Cont)
    |  grabHex(St,soFar,Cont) is
          Cont(St,soFar as char)

    fun readString(State) is let{
      fun readStr(St,soFar) where hedChar(St) has value X is switch X in {
        case '\\' is grabQtChar(nxSt(St),fn(cuSt,Ch)=>readStr(cuSt,cons of [Ch,..soFar]))
        case '\"' is report(stringTok(revImplode(soFar),deltaLoc(State,St)),nxSt(St))
        case '$' is interpolate(nxSt(St),list of [literalSegment(revImplode(soFar),deltaLoc(State,St))],displayMode)
        case '#' is interpolate(nxSt(St),list of [literalSegment(revImplode(soFar),deltaLoc(State,St))],convertMode)
        case Ch default is readStr(nxSt(St),cons of [Ch,..soFar])
      }

      fun interpolate(St,soFar,Mode) where hedChar(St) has value Ch is switch Ch in {
        case '\(' is bracketCont(St,fn(Text,ESt)=>
            readFormat(ESt,fn(Fmt,FSt)=>interpolateMore(FSt,list of [soFar..,interpolateElement(Mode,Text,Fmt,deltaLoc(St,FSt))])))
        case X where isIdentifierChar(X) is
          readIden(St,fn(Id,ESt)=>
            readFormat(ESt,fn(Fmt,FSt)=>interpolateMore(FSt,list of [soFar..,interpolateElement(Mode,Id,Fmt,deltaLoc(St,FSt))])))
      }

      fun readFormat(St,Cont) where hedChar(St) has value ':' is let{
            fun readFmt(cuSt,soFar) where hedChar(cuSt) has value hCh is switch hCh in {
                  case ':' is Cont(revImplode(soFar),nxSt(cuSt))
                  case Ch default is readFmt(nxSt(cuSt),cons of [Ch,..soFar])
                }
             |  readFmt(cuSt,soFar) default is Cont(revImplode(soFar),cuSt)
          } in readFmt(nxSt(St),cons of [])
       |  readFormat(St,Cont) default is Cont("",St)

      fun bracketCont(Stte,Cont) is let{
        fun bktCont(St,soFar,[Exp]) where hedChar(St) has value Exp is
              Cont(revImplode(cons of [Exp,..soFar]),nxSt(St))
         |  bktCont(St,soFar,[Exp,..ting]) where hedChar(St) has value Exp is
              bktCont(nxSt(St),cons of [Exp,..soFar],ting)
         |  bktCont(St,soFar,Exp) where hedChar(St) has value hCh is switch hCh in {
          case '\(' is bktCont(nxSt(St),cons of ['\(',..soFar],cons of ['\)',..Exp])
          case '\[' is bktCont(nxSt(St),cons of ['\[',..soFar],cons of ['\]',..Exp])
          case '\{' is bktCont(nxSt(St),cons of ['\{',..soFar],cons of ['\}',..Exp])
          case Ch default is bktCont(nxSt(St),cons of [Ch,..soFar],Exp)
        }
      } in bktCont(Stte,cons of [],cons of [])

      fun interpolateMore(SSt,segments) is let{
        fun stringSeg(St,soFar) where hedChar(St) has value hCh is switch hCh in {
          case '\\' is grabQtChar(nxSt(St),fn(cuSt,Ch)=>stringSeg(cuSt,cons of [Ch,..soFar]))
          case '\"' is report(interpolatedString(list of [segments..,literalSegment(revImplode(soFar),deltaLoc(SSt,St))],deltaLoc(State,St)),nxSt(St))
          case '$' is interpolate(nxSt(St),list of [segments..,literalSegment(revImplode(soFar),deltaLoc(SSt,St))],displayMode)
          case '#' is interpolate(nxSt(St),list of [segments..,literalSegment(revImplode(soFar),deltaLoc(SSt,St))],convertMode)
          case Ch default is stringSeg(nxSt(St),cons of [Ch,..soFar])
        }
      } in stringSeg(SSt,cons of [])
    } in readStr(nxSt(State),cons of [])

    fun report(Tk,St) is (Tk,St)
  } in skipToNxTok(tkSt)

  -- These function pick up the standard java notion of identifier
  fun isIdentifierStart(char(C)) is __isIdentifierStart(C)
  fun isIdentifierChar(char(C)) is __isIdentifierPart(C)

  private
  fun isHexDigit(X) is ('0'=<X and X=<'9') or ('a'=<X and X=<'f') or ('A'=<X and X=<'F')
  
  private
  fun isDigit('0') is true
   |  isDigit('1') is true
   |  isDigit('2') is true
   |  isDigit('3') is true
   |  isDigit('4') is true
   |  isDigit('5') is true
   |  isDigit('6') is true
   |  isDigit('7') is true
   |  isDigit('8') is true
   |  isDigit('9') is true
   |  isDigit(_) default is false

  fun hexDigitVal(X) where '0'=<X and X=<'9' is X as integer-'0' as integer
   |  hexDigitVal(X) where 'a'=<X and X=<'f' is X as integer-'a' as integer+10
   |  hexDigitVal(X) where 'A'=<X and X=<'F' is X as integer-'A' as integer+10

  revImplode has type (cons of char)=>string
  private fun revImplode(X) is string(__string_rev_implode(X))

  implementation pPrint over token is {
    fun ppDisp(Tok) is shTok(Tok)
  } using {
    fun shTok(idTok(idnt,Lc)) is ppSequence(0,cons of [ppStr("["), ppStr(idnt), ppStr("]")])
     |  shTok(integerTok(Ix,Lc)) is ppSequence(0,cons of [ppStr(Ix as string)])
     |  shTok(longTok(Lx,Lc)) is ppSequence(0,cons of [ppStr(Lx as string),ppStr("l")])
     |  shTok(floatTok(Dx,Lc)) is ppSequence(0,cons of [ppStr(Dx as string)])
     |  shTok(decimalTok(Dx,Lc)) is ppSequence(0,cons of [ppStr(Dx as string),ppStr("a")])
     |  shTok(charTok(Cx,Lc)) is ppDisp(Cx)
     |  shTok(stringTok(Sx,Lc)) is ppDisp(Sx)
     |  shTok(regexpTok(Sx,Lc)) is ppSequence(0,cons of [ppStr("\`"), ppStr(Sx), ppStr("\`")])
     |  shTok(interpolatedString(L,_)) is ppSequence(0,cons of [ppStr("\""), ppContents(L), ppStr("\"")])
     |  shTok(terminal) is ppStr("terminal")

    fun ppContents(L) is ppSequence(0,cons of {all ppEl(C) where C in L})

    fun ppEl(interpolateElement(displayMode,T,"",_)) is ppSequence(0,cons of [ppStr("\$"),ppStr(T),ppStr(";")])
     |  ppEl(interpolateElement(displayMode,T,F,_)) is ppSequence(0,cons of [ppStr("\$"),ppStr(T),ppStr(":"),ppStr(F),ppStr(";")])
     |  ppEl(interpolateElement(convertMode,T,"",_)) is ppSequence(0,cons of [ppStr("\#"),ppStr(T),ppStr(";")])
     |  ppEl(interpolateElement(convertMode,T,F,_)) is ppSequence(0,cons of [ppStr("\#"),ppStr(T),ppStr(":"),ppStr(F),ppStr(";")])
     |  ppEl(literalSegment(T,_)) is ppStr(T)

    fun showLc(Lc) is ppDisp(Lc)
  }

  fun tkLoc(tokenState{currLine=L; currOff=F; currPos=P},Ln) is
    someWhere{lineCount=L;lineOffset=F;charCount=P;length=Ln}

  fun deltaLoc(tokenState{currLine=L; currOff=F; currPos=P},tokenState{currPos=PE}) is 
    someWhere{lineCount=L;lineOffset=F;charCount=P;length=PE-P}

  -- Handle stream of tokens
  loadUri has type (uri)=>string
  fun loadUri(U) is string(__getUri(U))

  fun tokenize(U) is tokenState{
    text=explode(loadUri(U as uri))
    currLine = 1
    currOff = 0
    currPos = 0
  }

  fun stringTokens(S,Lc) is tokenState{
    text = explode(S)
    currLine = Lc.lineCount
    currOff = Lc.lineOffset
    currPos = 0
  }
}