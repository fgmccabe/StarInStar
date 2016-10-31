ast is package{
  -- Essentially a copy of the standard ast framework.
  public import location
  private import operators
  private import treemap

  public type ast is asName(srcLoc,string)
    or asInteger(srcLoc,integer)
    or asFloat(srcLoc,float)
    or asString(srcLoc,string)
    or asTuple(srcLoc,string,list of ast)
    or asApply(srcLoc,ast,ast)

  public implementation hasLocation over ast is {
    fun locOf(asName(L,_)) is L
     |  locOf(asInteger(L,_)) is L
     |  locOf(asFloat(L,_)) is L
     |  locOf(asString(L,_)) is L
     |  locOf(asApply(L,_,_)) is L
     |  locOf(asTuple(L,_,_)) is L
  }

  isName has type (ast) => option of string
  fun isName(asName(_,Nm)) is some(Nm)
   |  isName(_) default is none

  unary has type (srcLoc,string,ast) => ast
  fun unary(Lc,Op,Arg) is oneApply(Lc,asName(Lc,Op),Arg)

  isUnary has type (srcLoc,string,ast) <= ast
  ptn isUnary(Lc,Nm,E) from asApply(Lc,asName(_,Nm),asTuple(_,"()",list of [E]))

  oneApply has type (srcLoc,ast,ast) => ast
  fun oneApply(Lc,Op,Arg) is asApply(Lc,Op,asTuple(Lc,"()",list of [Arg]))

  bin has type (srcLoc,string,ast,ast) => ast
  fun bin(Lc,Op,Lhs,Rhs) is binApply(Lc,asName(Lc,Op),Lhs,Rhs)

  binApply has type (srcLoc,ast,ast,ast) => ast
  fun binApply(Lc,Op,Lhs,Rhs) is asApply(Lc,Op,asTuple(Lc,"()",list of [Lhs, Rhs]))

  isBinary has type (srcLoc,string,ast,ast) <= ast
  ptn isBinary(Lc,Nm,L,R) from asApply(Lc,asName(_,Nm),asTuple(_,"()",list of [L,R]))

  isTernary has type (srcLoc,string,ast,ast,ast) <= ast
  ptn isTernary(Lc,Nm,L,M,R) from asApply(Lc,asName(_,Nm),asTuple(_,"()",list of [L,M,R]))

  isQuad has type (srcLoc,string,ast,ast,ast,ast) <= ast
  ptn isQuad(Lc,Nm,L,M,M2,R) from asApply(Lc,asName(_,Nm),asTuple(_,"()",list of [L,M,M2,R]))

  nAry has type (srcLoc,string,list of ast)=>ast
  fun nAry(Lc,Op,Args) is asApply(Lc,asName(Lc,Op),asTuple(Lc,"()",Args))

  isApply has type (srcLoc,string,list of ast) <= ast
  ptn isApply(Lc,Op,Args) from asApply(Lc,asName(_,Op),asTuple(_,"()",Args))

  block has type (srcLoc,list of ast) => ast
  fun block(Lc,els) is asTuple(Lc,"{}",els)

  isBLock has type (srcLoc,list of ast) <= ast
  ptn isBlock(Lc,els) from asTuple(Lc,"{}",els)

  tple has type (srcLoc,list of ast) => ast
  fun tple(Lc,els) is asTuple(Lc,"()",els)

  deComma has type (ast) => list of ast
  fun deComma(isBinary(_,",",L,R)) is list of [L,..deComma(R)]
   |  deComma(T) default is list of [T]

  deParen has type (ast) => ast
  fun deParen(asTuple(_,"()",list of [E])) is E
   |  deParen(E) default is E

  implementation pPrint over ast is {
    fun ppDisp(T) is showTerm(T,2000)
  } using {
    showTerm has type (ast,integer) => pP
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
     |  showTerm(asFloat(_,Fx),_) is ppStr(Fx as string)
     |  showTerm(asString(_,Sx),_) is ppSequence(0,cons of [ ppStr("\""), ppStr(Sx), ppStr("\"")])
     |  showTerm(asTuple(_,Lbl,Els),_) is valof{
          if isBracket(Lbl,standardOps) matches some(BkSpec) then 
          	valis ppSequence(0,cons of [ ppStr(BkSpec.left), 
          	ppSequence(0,interleave(showEls(Els,BkSpec.inPrior),ppStr(BkSpec.seqOp))), 
            ppStr(BkSpec.right)])
          else
          	valis ppStr("**bad block**")
        }

    showEls has type (list of ast,integer) => cons of pP
    fun showEls(list of [],_) is cons of []
     |  showEls(list of [H,..T],Pr) is cons of [showTerm(H,Pr),.. showEls(T,Pr)]
  }
}