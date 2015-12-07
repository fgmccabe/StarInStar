ast is package{
  -- Essentially a copy of the standard ast framework.
  import location
  private import operators
  private import treemap

  type ast is asName(srcLoc,string)
    or asInteger(srcLoc,integer)
    or asLong(srcLoc,long)
    or asFloat(srcLoc,float)
    or asDecimal(srcLoc,decimal)
    or asChar(srcLoc,char)
    or asString(srcLoc,string)
    or asTuple(srcLoc,string,list of ast)
    or asApply(srcLoc,ast,ast)

  implementation hasLocation over ast is {
    locOf = astLocOf
  } using {
    fun astLocOf(asName(L,_)) is L
     |  astLocOf(asInteger(L,_)) is L
     |  astLocOf(asLong(L,_)) is L
     |  astLocOf(asFloat(L,_)) is L
     |  astLocOf(asDecimal(L,_)) is L
     |  astLocOf(asChar(L,_)) is L
     |  astLocOf(asString(L,_)) is L
     |  astLocOf(asApply(L,_,_)) is L
     |  astLocOf(asTuple(L,_,_)) is L
  }

  fun isName(asName(_,Nm)) is some(Nm)
   |  isName(_) default is none

  fun unary(Lc,Op,Arg) is oneApply(Lc,asName(Lc,Op),Arg)

  ptn isUnary(Lc,Nm,E) from asApply(Lc,asName(_,Nm),asTuple(_,"()",list of [E]))

  fun oneApply(Lc,Op,Arg) is asApply(Lc,Op,asTuple(Lc,"()",list of [Arg]))

  fun bin(Lc,Op,Lhs,Rhs) is binApply(Lc,asName(Lc,Op),Lhs,Rhs)

  fun binApply(Lc,Op,Lhs,Rhs) is asApply(Lc,Op,asTuple(Lc,"()",list of [Lhs, Rhs]))

  ptn isBinary(Lc,Nm,L,R) from asApply(Lc,asName(_,Nm),asTuple(_,"()",list of [L,R]))

  ptn isTernary(Lc,Nm,L,M,R) from asApply(Lc,asName(_,Nm),asTuple(_,"()",list of [L,M,R]))

  ptn isQuad(Lc,Nm,L,M,M2,R) from asApply(Lc,asName(_,Nm),asTuple(_,"()",list of [L,M,M2,R]))

  fun nAry(Lc,Op,Args) is asApply(Lc,asName(Lc,Op),asTuple(Lc,"()",Args))

  ptn isApply(Lc,Op,Args) from asApply(Lc,asName(_,Op),asTuple(_,"()",Args))

  fun block(Lc,els) is asTuple(Lc,"{}",els)

  ptn isBlock(Lc,els) from asTuple(Lc,"{}",els)

  fun tple(Lc,els) is asTuple(Lc,"()",els)

  fun deComma(isBinary(_,",",L,R)) is list of [L,..deComma(R)]
   |  deComma(T) default is list of [T]

  fun deParen(asTuple(_,"()",list of [E])) is E
   |  deParen(E) default is E

  implementation pPrint over ast is {
    fun ppDisp(T) is showTerm(T,2000)
  } using {
    fun showTerm(asApply(_,asName(_,Nm),asTuple(_,"()",list of [El])),Priority) is valof{
          if isPrefixOp(Nm,standardOps,Priority) matches some(Spec) then {
            if Spec.priority>Priority then
          	  valis ppSequence(0,cons of [ ppStr("("), ppStr(Nm), ppSpace, showTerm(El,Spec.right), ppStr(")")])
          	else
          	  valis ppSequence(0,cons of [ ppStr(Nm), ppSpace, showTerm(El,Spec.right)])
          }
          else if isPostfixOp(Nm,standardOps,2000) matches some(Spec) then {
            if Spec.priority>Priority then
          	  valis ppSequence(0,cons of [ ppStr("("), showTerm(El,Spec.left), ppSpace, ppStr(Nm), ppStr(")")])
          	else
          	  valis ppSequence(0,cons of [ showTerm(El,Spec.right), ppSpace, ppStr(Nm) ])
          } else if isBracket(Nm,standardOps) matches some(BkSpec) then 
          	valis ppSequence(0,cons of [ ppStr(BkSpec.left), showTerm(El,BkSpec.inPrior), ppStr(BkSpec.right)])
          else
          	valis ppSequence(0,cons of [ ppStr(Nm), ppStr("("), showTerm(El,999), ppStr(")")])
        }
     |  showTerm(asApply(_,asName(_,Nm),asTuple(_,"()",list of [L,R])),Priority) is valof{
          if isInfixOp(Nm,standardOps,Priority) matches some(Spec) then {
          	if Spec.priority>Priority then
          	  valis ppSequence(0,cons of [ ppStr("("), showTerm(L,Spec.right), ppSpace, ppStr(Nm), ppSpace, showTerm(R,Spec.right), ppStr(")")])
          	else
          	  valis ppSequence(0,cons of [ showTerm(L,Spec.right), ppSpace, ppStr(Nm), ppSpace, showTerm(R,Spec.right)])
          } 
          else
          	valis ppSequence(0,cons of [ ppStr(Nm), ppStr("("), showTerm(L,999), ppStr(", "), showTerm(R,999), ppStr(")")])
        }
     |  showTerm(asApply(_,Op,Args),_) is 
        	ppSequence(0,cons of [showTerm(Op,0), showTerm(Args,0)])
     |  showTerm(asName(_,Nm),_) where isOperator(Nm,standardOps,2000) is
        	ppSequence(0,cons of [ppStr("("), ppStr(Nm), ppStr(")")])
     |  showTerm(asName(_,Nm),_) is ppStr(Nm)
     |  showTerm(asInteger(_,Ix),_) is ppStr(Ix as string)
     |  showTerm(asLong(_,Ix),_) is ppStr(Ix as string)
     |  showTerm(asFloat(_,Fx),_) is ppStr(Fx as string)
     |  showTerm(asDecimal(_,Dx),_) is ppStr(Dx as string)
     |  showTerm(asChar(_,Cx),_) is ppSequence(0,cons of [ ppStr("'"), ppStr(Cx as string), ppStr("'")])
     |  showTerm(asString(_,Sx),_) is ppSequence(0,cons of [ ppStr("\""), ppStr(Sx), ppStr("\"")])
     |  showTerm(asTuple(_,Lbl,Els),_) is valof{
          if isBracket(Lbl,standardOps) matches some(BkSpec) then 
          	valis ppSequence(0,cons of [ ppStr(BkSpec.left), 
          	ppSequence(0,interleave(showEls(Els,BkSpec.inPrior),ppStr(BkSpec.seqOp))), 
            ppStr(BkSpec.right)])
          else
          	valis ppStr("**bad block**")
        }

    fun showEls(list of [],_) is cons of []
     |  showEls(list of [H,..T],Pr) is cons of [showTerm(H,Pr),.. showEls(T,Pr)]
  }
}