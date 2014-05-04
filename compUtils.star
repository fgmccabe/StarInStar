compUtils is package{
  private import ast;

  isUnary(T,Op) is isApply(T,1) and isName(applyOp(T),Op);

  isUnry(T) is isApply(T,1);

  unaryArg(T) is valof{
    assert isUnry(T);
    valis applyArg(T,0);
  }

  isBinary(T,Op) is isApply(T,2) and isName(applyOp(T),Op);
  isBinry(T) is isApply(T,2);

  binLhs(T) is valof{
    assert isBinry(T);
    valis applyArg(T,0);
  }
  binRhs(T) is valof{
    assert isBinry(T);
    valis applyArg(T,1);
  }

  isTernary(T,Op) is isApply(T,3) and isName(applyOp(T),Op);
  isTernry(T) is isApply(T,3);

  terLhs(T) is valof{
    assert isTernry(T);
    valis applyArg(T,0);
  }
  terMid(T) is valof{
    assert isTernry(T);
    valis applyArg(T,1);
  }
  terRhs(T) is valof{
    assert isTernry(T);
    valis applyArg(T,2);
  }

  isApply(asApply(_,_,A),Ar) is isTuple(A,Ar);
  isApply(_,_) default is false;

  applyOp(asApply(_,O,_)) is O;

  applyArg(asApply(_,_,T),Ix) is tupleEl(T,Ix);

  isName(asName(_,Id),IdX) is Id=IdX;
  isName(_,_) default is false;

  isTuple(asTuple(_,_,Els),Arity) is size(Els)=Arity;
  isTuple(_,_) default is false;

  tupleEl(asTuple(_,_,Els),Ix) is Els[Ix];
}