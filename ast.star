ast is package{
  -- Essentially a copy of the standard ast framework.
  import location;
  private import operators;
  private import maybe;
  private import treemap;

  type ast is asName(srcLoc,string)
  or asInteger(srcLoc,integer)
    or asLong(srcLoc,long)
    or asFloat(srcLoc,float)
    or asDecimal(srcLoc,decimal)
    or asChar(srcLoc,char)
    or asString(srcLoc,string)
    or asTuple(srcLoc,string,list of ast)
    or asApply(srcLoc,ast,ast);

  locOf(asName(L,_)) is L;
  locOf(asInteger(L,_)) is L;
  locOf(asLong(L,_)) is L;
  locOf(asFloat(L,_)) is L;
  locOf(asDecimal(L,_)) is L;
  locOf(asChar(L,_)) is L;
  locOf(asString(L,_)) is L;
  locOf(asApply(L,_,_)) is L;
  locOf(asTuple(L,_,_)) is L;

  unary(Lc,Op,Arg) is oneApply(Lc,asName(Lc,Op),Arg);

  isUnary(asApply(_,asName(_,Nm),asTuple(_,"()",list of {E})),Nm) is some(E);
  isUnary(_,_) default is none;

  oneApply(Lc,Op,Arg) is asApply(Lc,Op,asTuple(Lc,"()",list of {Arg}));

  bin(Lc,Op,Lhs,Rhs) is binApply(Lc,asName(Lc,Op),Lhs,Rhs);

  binApply(Lc,Op,Lhs,Rhs) is asApply(Lc,Op,asTuple(Lc,"()",list of {Lhs;Rhs}));

  isBinary(asApply(_,asName(_,Nm),asTuple(_,"()",list of {L;R})),Nm) is some((L,R));
  isBinary(_,_) default is none;

  nAry(Lc,Op,Args) is asApply(Lc,asName(Lc,Op),asTuple(Lc,"()",Args));

  block(Lc,els) is asTuple(Lc,"{}",els);

  tple(Lc,els) is asTuple(Lc,"()",els);

  implementation pPrint over ast is {
    ppDisp(T) is showTerm(T,2000);
  } using {
    showTerm(asApply(_,asName(_,Nm),asTuple(_,"()",list of {El})),Priority) is valof{
      if isPrefixOp(Nm,standardOps,Priority) matches Just(Spec) then {
	if Spec.priority>Priority then
	  valis ppSequence(0,cons of { ppStr("("); ppStr(Nm); ppSpace; showTerm(El,Spec.right); ppStr(")")})
	else
	  valis ppSequence(0,cons of { ppStr(Nm); ppSpace; showTerm(El,Spec.right)})
      } else if isPostfixOp(Nm,standardOps,2000) matches Just(Spec) then {
	if Spec.priority>Priority then
	  valis ppSequence(0,cons of { ppStr("("); showTerm(El,Spec.left); ppSpace; ppStr(Nm); ppStr(")")})
	else
	  valis ppSequence(0,cons of { showTerm(El,Spec.right);ppSpace;ppStr(Nm) })
      } else if isBracket(Nm,standardOps) matches Just(BkSpec) then 
	valis ppSequence(0,cons of { ppStr(BkSpec.left); showTerm(El,BkSpec.inPrior); ppStr(BkSpec.right)})
      else
	valis ppSequence(0,cons of { ppStr(Nm); ppStr("("); showTerm(El,999); ppStr(")")})
    };
    showTerm(asApply(_,asName(_,Nm),asTuple(_,"()",list of {L;R})),Priority) is valof{
      if isInfixOp(Nm,standardOps,Priority) matches Just(Spec) then {
	if Spec.priority>Priority then
	  valis ppSequence(0,cons of { ppStr("("); showTerm(L,Spec.right); ppSpace; ppStr(Nm); ppSpace; showTerm(R,Spec.right); ppStr(")")})
	else
	  valis ppSequence(0,cons of { showTerm(L,Spec.right); ppSpace; ppStr(Nm); ppSpace; showTerm(R,Spec.right)})
      } 
      else
	valis ppSequence(0,cons of { ppStr(Nm); ppStr("("); showTerm(L,999); ppStr(", ");showTerm(R,999);ppStr(")")})
    };
    showTerm(asApply(_,Op,Args),_) is 
	ppSequence(0,cons of {showTerm(Op,0); showTerm(Args,0) });
    showTerm(asName(_,Nm),_) where isOperator(Nm,standardOps,2000) is
	ppSequence(0,cons of {ppStr("("); ppStr(Nm); ppStr(")")});
    showTerm(asName(_,Nm),_) is ppStr(Nm);
    showTerm(asInteger(_,Ix),_) is ppStr(Ix as string);
    showTerm(asLong(_,Ix),_) is ppStr(Ix as string);
    showTerm(asFloat(_,Fx),_) is ppStr(Fx as string);
    showTerm(asDecimal(_,Dx),_) is ppStr(Dx as string);
    showTerm(asChar(_,Cx),_) is ppSequence(0,cons of {ppStr("'"); ppStr(Cx as string);ppStr("'")});
    showTerm(asString(_,Sx),_) is ppSequence(0,cons of {ppStr("\""); ppStr(Sx);ppStr("\"")});
    showTerm(asTuple(_,Lbl,Els),_) is valof{
      if isBracket(Lbl,standardOps) matches Just(BkSpec) then 
	valis ppSequence(0,cons of { ppStr(BkSpec.left); 
	 ppSequence(0,interleave(showEls(Els,BkSpec.inPrior),ppStr(BkSpec.seqOp))); 
	 ppStr(BkSpec.right)})
      else
	valis ppStr("**bad block**")
    };

    showEls(list of {},_) is cons of {};
    showEls(list of {H;..T},Pr) is cons of {showTerm(H,Pr);.. showEls(T,Pr)};
  }
}