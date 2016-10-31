lexer is package{
  private import location
  private import operators
  private import stream
  private import errors
  private import chars

  type token is idTok(string,srcLoc)
    or integerTok(integer,srcLoc)
    or floatTok(float,srcLoc)
    or stringTok(string,srcLoc)
    or regexpTok(string,srcLoc)
    or interpolatedString(list of interpolationElement,srcLoc)
    or terminal

  implementation hasLocation over token is {
    fun locOf(idTok(_,Lc)) is Lc
     |  locOf(integerTok(_,Lc)) is Lc
     |  locOf(floatTok(_,Lc)) is Lc
     |  locOf(stringTok(_,Lc)) is Lc
     |  locOf(regexpTok(_,Lc)) is Lc
     |  locOf(interpolatedString(_,Lc)) is Lc
     |  locOf(terminal) is missing
  }

  type interpolationElement is interpolateElement(interpolationMode,string,string,srcLoc) or literalSegment(string,srcLoc)

  type interpolationMode is displayMode or convertMode

  type tokenState is tokenState{
    text has type list of integer
    currLine has type integer
    currOff has type integer
    currPos has type integer
  }

  private
  hedChar has type (tokenState) => option of integer
  fun hedChar(tokenState{text=[Ch,.._]}) is some(Ch)
   |  hedChar(_) default is none

  private
  hedHedChar has type (tokenState) => option of integer
  fun hedHedChar(tokenState{text=[_,Ch,.._]}) is some(Ch)

  private hedHedHedChar has type (tokenState) => option of integer
  fun hedHedHedChar(tokenState{text=[_,_,Ch,.._]}) is some(Ch)

  private 
  nxSt has type (tokenState) => tokenState
  fun nxSt(tokenState{text=[Ch,..T];currLine=cuL;currOff=O;currPos=P}) is
        Ch=0c\n?
          tokenState{text=T;currLine=cuL+1;currOff=0;currPos=P+1} :
          tokenState{text=T;currLine=cuL;currOff=O+1;currPos=P+1}
   |  nxSt(St matching tokenState{text=[]}) is St

  private mvSt has type (tokenState,integer) => tokenState
  fun mvSt(tokenState{text=T;currLine=cuL;currOff=O;currPos=P},off) is
    tokenState{text=T[off:];currLine=cuL;currOff=O+off;currPos=P+off}

  private isTerminal has type (tokenState) => boolean
  fun isTerminal(tokenState{text=T}) is T=[]

  private isSpace has type (integer) => boolean
  fun isSpace(0c ) is true
   |  isSpace(0c\t) is true
   |  isSpace(_) default is false

  nextToken has type (tokenState,operators) => (token,tokenState)
  fun nextToken(tkSt,Ops) is let{

    skipToNxTok has type (tokenState) => (token,tokenState)
    fun skipToNxTok(St) where hedChar(St) has value hCh is
          switch hCh in {
            case 0c  is skipToNxTok(nxSt(St))
            case 0c\t is skipToNxTok(nxSt(St))
            case 0c\n is skipToNxTok(nxSt(St))
            case 0c- where hedHedChar(St) has value 0c- and 
                            hedHedHedChar(St) has value CC and isSpace(CC) is
                  lineComment(St)
            case 0c/ where hedHedChar(St) has value 0c* is
                  blockComment(mvSt(St,2))
            case _ default is nxTok(St)
          }
     |  skipToNxTok(St) default is nxTok(St)

    lineComment has type (tokenState) => (token,tokenState)
    fun lineComment(St) where hedChar(St) has value hCh is
          switch hCh in {
            case 0c\n is skipToNxTok(nxSt(St))
            case _ default is lineComment(nxSt(St))
          }
     |  lineComment(St) default is nxTok(St)

    fun blockComment(St) where hedChar(St) has value hCh is
          switch hCh in {
            case 0c* is switch hedHedChar(St) in {
              case some(0c/) is skipToNxTok(nxSt(nxSt(St)))
              case _ default is blockComment(nxSt(St))
            }
            case _ default is blockComment(nxSt(St))
    	  }
     |  blockComment(St) default is nxTok(St)

    nxTok has type (tokenState) => (token,tokenState)
    fun nxTok(St) where hedChar(St) has value hCh is
          switch hCh in {
            case 0c. where hedHedChar(St) has value nDCh and isDigit(nDCh) is readNumber(St)
            case 0c\" where hedHedChar(St) has value 0c\" and hedHedHedChar(St) has value 0c\" is
              readTripleQuoted(St)
            case 0c\" is readString(St)
            case 0c\` is readRegexp(St)
            case 0c0 where hedHedChar(St) has value 0cc is
                readChar(mvSt(St,2),
                  (nSt,ch)=>report(integerTok(ch,deltaLoc(St,nSt)),nSt))
            case 0c\\ is readIden(St,(Id,ISt)=>report(idTok(Id,deltaLoc(St,ISt)),ISt))
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
            case Ch where isIdentifierStart(Ch) is readIden(St,(Id,ISt)=>report(idTok(Id,deltaLoc(St,ISt)),ISt))
            case X default is valof{
              reportError("invalid char: $X/0x$(X):XXXX;)",list of [tkLoc(St,1)])
              valis nxTok(nxSt(St))
            }
          }
     |  nxTok(St) default is (terminal,St)

    fun readNumber(State) is let{
      fun readNum(St) where hedChar(St) has value hCh is switch hCh in {
          case 0c0 where hedHedChar(St) has value 0cx is readHex(mvSt(St,2),cons of [])
          case _ default is readDigits(St,cons of [],readMoreNum)
        }

      fun readHex(St,soFar) where hedChar(St) has value D and isHexDigit(D) is readHex(nxSt(St),cons of [D,..soFar])
       |  readHex(St,soFar) default is
            report(integerTok(hex2integer(revImplode(soFar)),deltaLoc(State,St)),St)

      fun readDigits(St,soFar,Cont) where hedChar(St) has value D and isDigit(D) is readDigits(nxSt(St),cons of [D,..soFar],Cont)
       |  readDigits(St,soFar,Cont) is Cont(St,soFar)

      fun readMoreNum(St,soFar) where hedChar(St) has value 0c. is readDigits(nxSt(St),cons of [0c.,..soFar],readExponent)
       |  readMoreNum(St,soFar) default is
            report(integerTok(revImplode(soFar) as integer,deltaLoc(State,St)),St)

      fun readExponent(St,soFar) where hedChar(St) has value 0ce and hedHedChar(St) has value 0c- is
            readDigits(mvSt(St,2),cons of [0c-,0ce,..soFar],mkFloat)
       |  readExponent(St,soFar) where hedChar(St) has value 0ce is
            readDigits(nxSt(St),cons of [0ce,..soFar],mkFloat)
       |  readExponent(St,soFar) default is mkFloat(St,soFar)

      fun mkFloat(St,soFar) is report(floatTok(revImplode(soFar) as float,deltaLoc(State,St)),St)
    } in readNum(State)

    fun readIden(State,Cont) is let{
      fun readId() where hedChar(State) has value F and isIdentifierStart(F) is readMore(nxSt(State),cons(F,nil))
       |  readId() where hedChar(State) has value 0c\\ is
            grabQtChar(nxSt(State),(cuSt,Ch) => readMore(cuSt,cons of [Ch]))

      fun readMore(St,Id) where hedChar(St) has value C and isIdentifierChar(C) is
            readMore(nxSt(St),cons of [C,..Id])
       |  readMore(St,Id) where hedChar(St) has value 0c\\ is
            grabQtChar(nxSt(St),(cuSt,Ch) => readMore(cuSt,cons of [Ch,..Id]))
       |  readMore(St,Id) default is Cont(revImplode(Id),St)
    } in readId()

    fun readTripleQuoted(State) is let{
      fun readQuoted(St,soFar) where hedChar(St) has value 0c\" and hedHedChar(St) has value 0c\" and hedHedHedChar(St) has value 0c\" is
            report(stringTok(revImplode(soFar),deltaLoc(State,mvSt(St,3))),mvSt(St,3))
       |  readQuoted(St,soFar) where hedChar(St) has value hCh is readQuoted(nxSt(St),cons of [hCh,..soFar])
       |  readQuoted(St,soFar) where hedChar(St) = none is
            report(stringTok(revImplode(soFar),deltaLoc(State,St)),St)
    } in readQuoted(mvSt(State,3),cons of [])

    fun readChar(St,Cont) where hedChar(St) has value 0c\\ is
          grabQtChar(nxSt(St),Cont)
     |  readChar(St,Cont) where hedChar(St) has value 0c\n is valof{
          reportError("unexpected newline",list of [tkLoc(St,1)])
          valis report(integerTok(0c\n,tkLoc(St,1)),nxSt(St))
        }
     |  readChar(St,Cont) where hedChar(St) has value hCh is Cont(nxSt(St),hCh)

    fun readRegexp(State) is let{
      fun readReg(St,soFar) where hedChar(St) has value 0c\` is
            report(regexpTok(revImplode(soFar),deltaLoc(State,St)),nxSt(St))
       |  readReg(St,soFar) where hedChar(St) has value 0c\\ is
            grabQtChar(St,(cuSt,Ch)=>readReg(cuSt,cons of [Ch,..soFar]))
       |  readReg(St,soFar) where hedChar(St) has value nCh is readReg(nxSt(St),cons of [nCh,..soFar])
    } in readReg(nxSt(State),cons of [])

    fun grabQtChar(St,Cont) where hedChar(St) has value Ch is switch Ch in {
      case 0cb is Cont(nxSt(St),0c\b)
      case 0cd is Cont(nxSt(St),0c\d)
      case 0ce is Cont(nxSt(St),0c\e)
      case 0cf is Cont(nxSt(St),0c\f)
      case 0cn is Cont(nxSt(St),0c\n)
      case 0cr is Cont(nxSt(St),0c\r)
      case 0ct is Cont(nxSt(St),0c\t)
      case 0c\" is Cont(nxSt(St),0c\")
      case 0c\' is Cont(nxSt(St),0c\')
      case 0cu is grabHex(nxSt(St),0,Cont)
      case X default is Cont(nxSt(St),X)
    }

    fun grabHex(St,soFar,Cont) where hedChar(St) has value 0c; is Cont(nxSt(St),soFar)
     |  grabHex(St,soFar,Cont) where hedChar(St) has value X and isHexDigit(X) is
          grabHex(nxSt(St),soFar*16+hexDigitVal(X),Cont)
    |  grabHex(St,soFar,Cont) is Cont(St,soFar)

    fun readString(State) is let{
      fun readStr(St,soFar) where hedChar(St) has value X is switch X in {
        case 0c\\ is grabQtChar(nxSt(St),(cuSt,Ch)=>readStr(cuSt,cons of [Ch,..soFar]))
        case 0c\" is report(stringTok(revImplode(soFar),deltaLoc(State,St)),nxSt(St))
        case 0c$ is interpolate(nxSt(St),list of [literalSegment(revImplode(soFar),deltaLoc(State,St))],displayMode)
        case 0c# is interpolate(nxSt(St),list of [literalSegment(revImplode(soFar),deltaLoc(State,St))],convertMode)
        case Ch default is readStr(nxSt(St),cons of [Ch,..soFar])
      }

      fun interpolate(St,soFar,Mode) where hedChar(St) has value Ch is switch Ch in {
        case 0c\( is bracketCont(St,(Text,ESt)=>
            readFormat(ESt,(Fmt,FSt)=>interpolateMore(FSt,[soFar..,interpolateElement(Mode,Text,Fmt,deltaLoc(St,FSt))])))
        case X where isIdentifierChar(X) is
          readIden(St,(Id,ESt)=>
            readFormat(ESt,(Fmt,FSt)=>interpolateMore(FSt,[soFar..,interpolateElement(Mode,Id,Fmt,deltaLoc(St,FSt))])))
        case X default is valof{
              reportError("invalid char: $X/0x$(X):XXXX;)",[tkLoc(St,1)])
          valis readStr(nxSt(St),[])
        }
      }

      fun readFormat(St,Cont) where hedChar(St) has value 0c: is let{
            fun readFmt(cuSt,soFar) where hedChar(cuSt) has value hCh is switch hCh in {
                  case 0c: is Cont(revImplode(soFar),nxSt(cuSt))
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
          case 0c\( is bktCont(nxSt(St),cons of [0c\(,..soFar],cons of [0c\),..Exp])
          case 0c\[ is bktCont(nxSt(St),cons of [0c\[,..soFar],cons of [0c\],..Exp])
          case 0c\{ is bktCont(nxSt(St),cons of [0c\{,..soFar],cons of [0c\},..Exp])
          case Ch default is bktCont(nxSt(St),cons of [Ch,..soFar],Exp)
        }
      } in bktCont(Stte,cons of [],cons of [])

      fun interpolateMore(SSt,segments) is let{
        fun stringSeg(St,soFar) where hedChar(St) has value hCh is switch hCh in {
          case 0c\\ is grabQtChar(nxSt(St),(cuSt,Ch)=>stringSeg(cuSt,cons of [Ch,..soFar]))
          case 0c\" is report(interpolatedString(list of [segments..,literalSegment(revImplode(soFar),deltaLoc(SSt,St))],deltaLoc(State,St)),nxSt(St))
          case 0c$ is interpolate(nxSt(St),list of [segments..,literalSegment(revImplode(soFar),deltaLoc(SSt,St))],displayMode)
          case 0c# is interpolate(nxSt(St),list of [segments..,literalSegment(revImplode(soFar),deltaLoc(SSt,St))],convertMode)
          case Ch default is stringSeg(nxSt(St),cons of [Ch,..soFar])
        }
      } in stringSeg(SSt,cons of [])
    } in readStr(nxSt(State),cons of [])

    fun report(Tk,St) is (Tk,St)
  } in skipToNxTok(tkSt)

  private
  isHexDigit has type (integer) => boolean
  fun isHexDigit(X) is (0c0=<X and X=<0c9) or (0ca=<X and X=<0cf) or (0cA=<X and X=<0cF)
  
  private
  isDigit has type (integer) => boolean
  fun isDigit(0c0) is true
   |  isDigit(0c1) is true
   |  isDigit(0c2) is true
   |  isDigit(0c3) is true
   |  isDigit(0c4) is true
   |  isDigit(0c5) is true
   |  isDigit(0c6) is true
   |  isDigit(0c7) is true
   |  isDigit(0c8) is true
   |  isDigit(0c9) is true
   |  isDigit(_) default is false

  hexDigitVal has type (integer) => integer
  fun hexDigitVal(X) where 0c0=<X and X=<0c9 is X as integer-0c0 as integer
   |  hexDigitVal(X) where 0ca=<X and X=<0cf is X as integer-0ca as integer+10
   |  hexDigitVal(X) where 0cA=<X and X=<0cF is X as integer-0cA as integer+10

  revImplode has type (cons of integer)=>string
  private fun revImplode(X) is implode(reverse(X))

  implementation pPrint over token is {
    fun ppDisp(Tok) is shTok(Tok)
  } using {
    fun shTok(idTok(idnt,Lc)) is ppSequence(0,cons of [ppStr("["), ppStr(idnt), ppStr("]")])
     |  shTok(integerTok(Ix,Lc)) is ppSequence(0,cons of [ppStr(Ix as string)])
     |  shTok(floatTok(Dx,Lc)) is ppSequence(0,cons of [ppStr(Dx as string)])
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

  tkLoc has type (tokenState,integer) => srcLoc
  fun tkLoc(tokenState{currLine=L; currOff=F; currPos=P},Ln) is
    someWhere{lineCount=L;lineOffset=F;charCount=P;length=Ln}

  deltaLoc has type (tokenState,tokenState) => srcLoc
  fun deltaLoc(tokenState{currLine=L; currOff=F; currPos=P},tokenState{currPos=PE}) is 
    someWhere{lineCount=L;lineOffset=F;charCount=P;length=PE-P}

  -- Handle stream of tokens
  loadUri has type (uri)=>string
  fun loadUri(U) is string(__getUri(U))

  tokenize has type (uri) => tokenState
  fun tokenize(U) is tokenState{
    text=explode(loadUri(U))
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