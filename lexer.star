lexer is package{
  private import location;
  private import errors;
  private import operators;
  private import treemap;

  type token is idTok(string,srcLoc)
  or integerTok(integer,srcLoc)
    or longTok(long,srcLoc)
    or floatTok(float,srcLoc)
    or decimalTok(decimal,srcLoc)
    or charTok(char,srcLoc)
    or stringTok(string,srcLoc)
    or regexpTok(string,srcLoc)
    or terminal;
  
  tokenize(SrcText,Uri,StartLc) is let{
    locOf((ChrCount,Ln,Off),C) is someWhere{
      uri=Uri;charCount=ChrCount;
      lineCount=Ln;lineOffset=Off;
      length=C
    };
    
    nxtLoc((Count,Ln,Off),C) is (Count+C,Ln,Off+C);
    nxtLne((Count,Ln,Off)) is (Count+1,Ln+1,0);

    skipComments([' ',..L], Lc) is skipComments(L,nxtLoc(Lc,1));
    skipComments(['\t',..L], Lc) is skipComments(L,nxtLoc(Lc,1));
    skipComments(['\n',..L], Lc) is skipComments(L,nxtLne(Lc));
    skipComments(['-','-',' ',..L], Lc) is lineComment(L,nxtLoc(Lc,3));
    skipComments(['-','-','\t',..L], Lc) is lineComment(L,nxtLoc(Lc,3));
    skipComments(['/','*',..L], Lc) is blockComment(L,nxtLoc(Lc,2));
    skipComments(L,Lc) default is (L,Lc);
    
    lineComment(['\n',..L],Lc) is skipComments(L,nxtLne(Lc));
    lineComment([_,..L],Lc) is lineComment(L,nxtLoc(Lc,1));
    lineComment(L,Lc) default is (L,Lc);
    
    blockComment(['*','/',..L],Lc) is skipComments(L,nxtLoc(Lc,2));
    blockComment(['\n',..L],Lc) is blockComment(L,nxtLne(Lc));
    blockComment([_,..L],Lc) is blockComment(L,nxtLoc(Lc,1));
    blockComment(L,Lc) default is (L,Lc);
    
    reportNext(terminal,Txt,Lc) is cons of [terminal];
    reportNext(Tkn,Txt,Lc) is cons of [Tkn,..tokens(Txt,Lc)]
    
    tokens(Text,Lc) is nxtToken(Text,Lc,reportNext);

    nxtToken(Text,Lc,Cont) is valof{
      (nText,nLc) is skipComments(Text,Lc);
      valis hedToken(nText,nLc,Cont);
    };

    reportId(Id,Count,Text,Lc,Cont) is filter(Cont,idTok(Id,locOf(Lc,Count)),Text,nxtLoc(Lc,Count));

    hedToken(S matching (['.',D,..L]),Lc,Cont) where isDigit(D) is 
      readNumber(S,Lc,Cont);
    hedToken(['\'','s','\'',..L],Lc,Cont) is filter(Cont,charTok('s',locOf(Lc,3)),L,nxtLoc(Lc,3));
    hedToken(['\'','n','\'',..L],Lc,Cont) is filter(Cont,charTok('n',locOf(Lc,3)),L,nxtLoc(Lc,3));
    hedToken(['\'','s',..L],Lc,Cont) is reportId("'s",2,L,Lc,Cont);
    hedToken(['\'','n',..L],Lc,Cont) is reportId("'n",2,L,Lc,Cont);
    hedToken(Text matching (['\'',.._]),Lc,Cont) is readChar(Text,Lc,Cont);
    hedToken(['"','"','"',..L],Lc,Cont) is readTripleQuoted(L,cons of [], 0, nxtLoc(Lc,3),Cont);
    hedToken(['\"',..L],Lc,Cont) is readString(L,nxtLoc(Lc,1),Cont);
    hedToken(['0','c',..L],Lc,Cont) where readCh(L,Lc) matches ([Ch], L1, Cx) is
      filter(Cont,integerTok(Ch as integer,locOf(Lc,Cx+2)),L1,nxtLoc(Lc,Cx+2));
    hedToken(['\`',..L],Lc,Cont) is readRegexp(['\`',..L],Lc,Cont);
    hedToken(['\\',..L],Lc,Cont) is readIden(['\\',..L],Lc,Cont);
    
    hedToken(S matching [D,..L],Lc,Cont) where isDigit(D) is readNumber(S,Lc,Cont);
    
    hedToken([Ch,..L],Lc,Cont) where isLeadInChar(Ch) is valof{
      FG is firstGraph(Ch);
      (Tok,Rest,nLc) is followGraph(L,string of [Ch],isTermGraph(FG)?(string of [Ch],1,L)|("",0,L),FG,Lc,1);
      valis filter(Cont,Tok,Rest,nLc);
    };

    hedToken([X,..L],Lc,Cont) where isIdentifierStart(X) is readIden([X,..L],Lc,Cont);
    hedToken([X,..L],Lc,Cont) is valof{
      reportError("invalid char: $X/0x$(X as integer):XXXX;)",list of [locOf(Lc,1)]);
      valis hedToken(L,nxtLoc(Lc,1),Cont);
    };
    
    hedToken([],Lc,Cont) is filter(Cont,terminal,[],Lc);
    
    followGraph(Chars matching ([Ch,..L]),SoFar,Found,M,Lc,Ix) where isValidNextChar(Ch,M) is
	  followGraph(L,string of [SoFar..,Ch],(isTermGraph(M)?(SoFar,Ix,Chars)|Found),nextCharMap(Ch,M),Lc,Ix+1);
    followGraph(Chars,SoFar,_,M,Lc,Ix) where isTermGraph(M) is (idTok(revImplode(SoFar),locOf(Lc,Ix)),Chars,nxtLoc(Lc,Ix));
    followGraph(_,_,(Tk,Ix,Chars),M,Lc,_) is (idTok(Tk,locOf(Lc,Ix)),Chars,nxtLoc(Lc,Ix));
    
    -- These function pick up the standard java notion of identifier
    isIdentifierStart(char(C)) is __isIdentifierStart(C);
    isIdentifierChar(char(C)) is __isIdentifierPart(C);

    readIden(Ls,Lc,Cont) is let{
      readId([F,..L]) where isIdentifierStart(F) is readMore(L,cons(F,nil),1);
      readId(['\\',..L]) is valof{
        (F,L1,Cnt1) is grabQtChar(L,nil,1);
        valis readMore(L1,F,Cnt1);
      }
      readMore([C,..L],Id,Cx) where isIdentifierChar(C) is
          readMore(L,cons(C,Id),Cx+1);
      readMore(['\\',..L],Id,Cx) is valof{
        (Idx,L1,Cnt1) is grabQtChar(L,Id,Cx+1);
        valis readMore(L1,Idx,Cnt1);
      };
      readMore(L,Id,Cnt) default is reportId(revImplode(Id),Cnt,L,Lc,Cont);
    } in readId(Ls);

    readChar(['\'',..L],Lc,Cont) where readCh(L,Lc) matches ([Ch], ['\'',..L1], Cx) is
      filter(Cont,charTok(Ch,locOf(Lc,Cx+2)),L1,nxtLoc(Lc,Cx+2));

    readCh(['\\',..L],Lc) is grabQtChar(L,nil,1);
    readCh([A,..L],Lc) is ([A],L,1);

    readString(Ls,Lc,Cont) is let{
      readStr(['\\',..L], Str, Cx) is valof{
        (St,L1,Cnt1) is grabQtChar(L,Str,Cx+1);
        valis readStr(L1,St,Cnt1);
      };
      readStr(['\"',..L],Str,Cx) is 
        filter(Cont,stringTok(revImplode(Str),locOf(Lc,Cx+1)),L,nxtLoc(Lc,Cx+1));
      readStr(['\$',..L], Str, Cx) is 
        interpolate(L,Str,Cx,"\$display");
      readStr(['\#',..L],Str,Cx) is 
    	  interpolate(L,Str,Cx,"\#as");
      readStr([C,..L], Str, Cx) is readStr(L,cons(C,Str),Cx+1);

      interpolate(['\(',..L],Str,Cx,Code) is valof{
        var nCont is bracketCont(")",(function(Text,nxLc) is readFormat(Text,nxLc)));
	
      	var nxtLc is nxtLoc(Lc,Cx);
      	var Rest is nxtToken(L,nxtLc,nCont);

        valis prefixSegment(Str,Cx,nxtLc,
          cons of [
            idTok(Code,locOf(nxtLc,1)),
            idTok("\(",locOf(nxtLc,1)),..Rest])
        }
      interpolate(L, Str, Cx,Code) is valof{
      	var nCont is (fn(Tkn,TL,nxtLc) => 
    	     prefixSegment(Str,Cx,nxtLc,
      		   cons of [
      		     idTok(Code,locOf(nxtLc,1)),
      		     Tkn,..readFormat(TL,nxtLc)]));
      	valis readIden(L,nxtLoc(Lc,Cx),nCont);
      }

      prefixSegment(Str,_,sLc,Rest) where isEmpty(Str) is Rest;
      prefixSegment(Str,Cx,sLc,Rest) default is cons of [stringTok(revImplode(Str),locOf(sLc,Cx)),
      	idTok("++",locOf(nxtLoc(sLc,Cx),2)),..Rest];

      readFormat([':',..L],nLc) is let{
      	readFmt([';',..Text],SoFar,Cx) is 
    	    cons of [idTok(":",locOf(nLc,1)),
          	      stringTok(revImplode(SoFar),locOf(nLc,Cx+2)),..restOfString(Text,nxtLoc(nLc,Cx+2))];
      	readFmt([],SoFar,Cx) is 
    	    cons of [idTok(":",locOf(nLc,1)),
          	      stringTok(revImplode(SoFar),locOf(nLc,Cx+2)),
          	      terminal];
      	readFmt([Ch,..Txt],SoFar,Cx) is readFmt(Txt,cons of [Ch,..SoFar],Cx+1);
      } in readFmt(L,cons of [],0);
      readFormat(Text,nLc) default is restOfString(Text,nLc);

      restOfString(Text,nLc) is cons of [idTok("++",locOf(nLc,2)),..readString(Text,nLc,Cont)];

      -- This Cnt is not the same thing as the outer Cont
      bracketCont(Closer,Rdr) is let{
      	cont(Tk matching idTok(Cl,_),Text,nxtLc) where Cl=Closer is
      	    cons of [Tk,..Rdr(Text,nxtLc)];
      	cont(Tk,Text,nxtLc) is valof{
      	  var nxtCnt is case Tk in {
      	    idTok("(",_) is bracketCont(")",rdr);
      	    idTok("[",_) is bracketCont("]",rdr);
      	    idTok("{",_) is bracketCont("}",rdr);
      	    _ default is cont;
      	  };
      	  valis cons of [Tk,..nxtToken(Text,nxtLc,nxtCnt)]
      	};
      	rdr(Text,nxLc) is nxtToken(Text,nxLc,cont);
      } in cont;
    } in readStr(Ls,nil,1);

    readTripleQuoted(['"','"','"',..L],Str,Cx,Lc,Cont) is
      filter(Cont,stringTok(revImplode(Str),locOf(Lc,Cx+3)),L,nxtLoc(Lc,Cx+3));
    readTripleQuoted([Ch,..L],Str,Cx,Lc,Cont) is
      readTripleQuoted(L,cons of [Ch,..Str],Cx+1,Lc,Cont);

    readRegexp(['\`',..Ls],Lc,Cont) is let{
      readReg(['\\',..L],Str,Cx) is valof{
        (St,L1,Cnt1) is grabQtChar(L,Str,Cx+1);
        valis readReg(L1,St,Cnt1);
      };
      readReg(['\`',..L],Str,Cx) is 
        filter(Cont,regexpTok(revImplode(Str),locOf(Lc,Cx+1)),L,nxtLoc(Lc,Cx+1));
      readReg([C,..L],Str,Cx) is readReg(L,cons(C,Str),Cx+1);
    } in readReg(Ls,nil,1);

    bktPairs is list of [('(',')'), ('[',']'), ('{','}') ];
    
    grabQtChar(['b',..L],Id,Cx) is (cons('\b',Id),L,Cx+1);
    grabQtChar(['d',..L],Id,Cx) is (cons('\d',Id),L,Cx+1);
    grabQtChar(['e',..L],Id,Cx) is (cons('\e',Id),L,Cx+1);
    grabQtChar(['f',..L],Id,Cx) is (cons('\f',Id),L,Cx+1);
    grabQtChar(['n',..L],Id,Cx) is (cons('\n',Id),L,Cx+1);
    grabQtChar(['r',..L],Id,Cx) is (cons('\r',Id),L,Cx+1);
    grabQtChar(['t',..L],Id,Cx) is (cons('\t',Id),L,Cx+1);
    grabQtChar(['\"',..L],Id,Cx) is (cons('\"',Id),L,Cx+1);
    grabQtChar(['\'',..L],Id,Cx) is (cons('\'',Id),L,Cx+1);
    grabQtChar(['\$',..L],Id,Cx) is (cons('\$',Id),L,Cx+1);
    grabQtChar(['\#',..L],Id,Cx) is (cons('\#',Id),L,Cx+1); 
    grabQtChar(['\\',..L],Id,Cx) is (cons('\\',Id),L,Cx+1);
    grabQtChar(['+',..L],Id,Cx) is grabHex(L,Id,Cx+1,0);
    grabQtChar(['u',..L],Id,Cx) is grabHex(L,Id,Cx+1,0);
    grabQtChar([C,..L],Id,Cx) is (cons(C,Id),L,Cx+1);

    grabHex([';',..L],Id,Hx,Cx) is (cons(Hx as char,Id),L,Cx+1);
    grabHex([X,..L],Id,Hx,Cx) where isHexDigit(X) is 
      grabHex(L,Id,Hx*16+hexDigitVal(X),Cx+1);
    grabHex(L,Id,Hx,Cx) is (cons(Hx as char,Id),L,Cx);

    isHexDigit(X) is ('0'<=X and X<='9') or ('a'<=X and X<='f') or ('A'<=X and X<='F');
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

    readNumber(Str,Lc,Cont) is let{
      readNum(['0', 'x',..L],Cx) is readHex(L,"",2);
      readNum(L,Cx) is readMoreNum(readDigits(L,"",Cx));

      readDigits([D,..L],NumSoFar,Count) where isDigit(D) is readDigits(L,string of [NumSoFar..,D],Count+1);
      readDigits(L,NumSoFar,Count) is (L,NumSoFar,Count);

      readHex([X,..L],Hx,Cx) where isHexDigit(X) is 
        readHex(L,string of [Hx..,X],Cx+1);
      readHex(['l',..L],Hx,Cx) is reportNext(longTok(hex2long(Hx),locOf(Lc,Cx+1)),L,nxtLoc(Lc,Cx+1));
      readHex(['L',..L],Hx,Cx) is reportNext(longTok(hex2long(Hx),locOf(Lc,Cx+1)),L,nxtLoc(Lc,Cx+1));
      readHex(L,Hx,Cx) is reportNext(integerTok(hex2integer(Hx),locOf(Lc,Cx)),L,nxtLoc(Lc,Cx));

      readMoreNum((['.',..L],Nm,Cx)) is 
        readExponent(readDigits(L,string of [Nm..,'.'],Cx+1));
      readMoreNum((['l',..L],Nm,Cx)) is 
        filter(Cont,longTok(Nm as long,locOf(Lc,Cx+1)),L,nxtLoc(Lc,Cx+1));
      readMoreNum((['L',..L],Nm,Cx)) is 
      	filter(Cont,longTok(Nm as long,locOf(Lc,Cx+1)),L,nxtLoc(Lc,Cx+1));
      readMoreNum((L,Nm,Cx)) is 
      	filter(Cont,integerTok(Nm as integer,locOf(Lc,Cx)),L,nxtLoc(Lc,Cx));

      readExponent((['e','-',..L],Nm,Cx)) is valof{
        (L1,NmE,Cx1) is readDigits(L,string of [Nm..,'e','-'],Cx+2);
        valis filter(Cont,floatTok(NmE as float,locOf(Lc,Cx1)),L1,nxtLoc(Lc,Cx1));
      }
      readExponent((['e',..L],Nm,Cx)) is valof{
        (L1,NmE,Cx1) is readDigits(L,string of [Nm..,'e'],Cx+1);
        valis filter(Cont,floatTok(NmE as float,locOf(Lc,Cx1)),L1,nxtLoc(Lc,Cx1));
      }
      readExponent((['a',..L],Nm,Cx)) is
      	filter(Cont,decimalTok(Nm as decimal,locOf(Lc,Cx+1)),L,nxtLoc(Lc,Cx+1));
      readExponent((['A',..L],Nm,Cx)) is 
      	filter(Cont,decimalTok(Nm as decimal,locOf(Lc,Cx+1)),L,nxtLoc(Lc,Cx+1));
      readExponent((L,Nm,Cx)) is 
      	filter(Cont,floatTok(Nm as float,locOf(Lc,Cx)),L,nxtLoc(Lc,Cx));
    } in readNum(Str,0);
  } in tokens(SrcText,StartLc);

  private filter is let{
    type state is idle or gotHash or gotOp or gotParen;
    var currState := idle;

    handle(Cont,Tk matching idTok(Nm,_),Rest,nxLc) is valof{
      case currState in {
        idle where Nm="\#" do
    	    currState := gotHash;
        gotHash where Nm="prefix" or Nm="infix" or Nm="postfix" or Nm="prefixAssoc" or
          	Nm="left" or Nm="right" or Nm="postfixAssoc" do
    	    currState := gotOp;
      	gotOp where Nm="\(" do
    	    currState := gotParen;
      	_ default do
    	    currState := idle;
      };
      valis Cont(Tk,Rest,nxLc)
    };
    handle(Cont, Tk matching stringTok(Op,_),Rest,nxLc) where currState=gotParen is valof{
      addStdGrph(Op);
      currState := idle;
      valis Cont(Tk,Rest,nxLc)
    }
    handle(Cont,Tk,Rest,nxLc) default is valof{
      currState := idle;
      valis Cont(Tk,Rest,nxLc)
    }
  } in handle;

  multiNextTok has type (list of token,operators) => (token,list of token);
  multiNextTok([],_) is (terminal,list of []);
  multiNextTok([Tk matching idTok(Id,Loc1),..R],Ops) where present Ops.multiops[Id] is valof{
    var (list of [_,..Toks],Res) is Ops.multiops[Id];
    
    valis followMulti(Toks,R,Res,list of [Tk]);
  }

  -- process sequence of tokens looking for multi-word tokens
  multiNextTok([Tk,..R],_) default is (Tk,R);

  private 
  followMulti(list of [],R,Res,Toks) is (idTok(Res,mergeLocs(Toks)),R);
  followMulti(list of [Frag,..Frags],list of [Tk matching idTok(Frag,Lc),..R],Res,Toks) is
    followMulti(Frags,R,Res,list of [Toks..,Tk]);
  followMulti(_,R,_,list of [Tk,..Oks]) is (Tk,Oks++R);

  mergeLocs(list of []) is missing;
  mergeLocs(list of [idTok(_,L0),..Tks]) where Tks matches [_..,idTok(_,Ln)] is mergeLocation(L0,Ln);
  mergeLocs(list of [idTok(_,L0)]) is L0; 

  private revImplode(X) is string(__string_rev_implode(X));

  implementation pPrint over token is {
    ppDisp(Tok) is shTok(Tok);
  } using {
    shTok(idTok(idnt,Lc)) is ppSequence(0,cons of [ppStr("["), ppStr(idnt), ppStr("]")]);
    shTok(integerTok(Ix,Lc)) is ppSequence(0,cons of [ppStr(Ix as string)]);
    shTok(longTok(Lx,Lc)) is ppSequence(0,cons of [ppStr(Lx as string)]);
    shTok(floatTok(Dx,Lc)) is ppSequence(0,cons of [ppStr(Dx as string)]);
    shTok(decimalTok(Dx,Lc)) is ppSequence(0,cons of [ppStr(Dx as string)]);
    shTok(charTok(Cx,Lc)) is ppSequence(0,cons of [ppStr("'"), ppStr(Cx as string), ppStr("'")]);
    shTok(stringTok(Sx,Lc)) is ppDisp(Sx);
    shTok(regexpTok(Sx,Lc)) is ppSequence(0,cons of [ppStr("\`"), ppStr(Sx), ppStr("\`")]);
    shTok(terminal) is ppStr("terminal");

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
  tokenLoc(terminal) is missing;
}