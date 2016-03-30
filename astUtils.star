astUtils is package{
  /*
  * Utility programs to help process ast terms
  */
  private import ast
  private import good


  private import lexer;
  private import operators;
  private import opgrammar;

  fun parseFile(File) is valof{
    def tokens is tokenize(File)
    def (Rest,Pr,T) is term(tokens,2000,standardOps);

    valis T
  }

  fun parseString(Text) is valof {
    def tokens is stringTokens(Text,someWhere{lineCount = 0; lineOffset=0; charCount = 0; length = size(Text)})

    def (_,_,T) is term(tokens,2000,standardOps)
    valis T
  }

  ptn isFunDef(Lc,Eqns) from asApply(Lc,asName(_,"fun"),asTuple(_,_,list of [Eqns]))

  ptn isLambdaAst(Lc,Lhs,Rhs) from asApply(Lc,asName(_,"=>"),asTuple(_,_,list of [Lhs,Rhs]))

  ptn isMemoAst(Lc,Rhs) from asApply(Lc,asName(_,"memo"),asTuple(_,_,list of [Rhs]))

  ptn isMemoDef(Lc,Lhs,Rhs) from isDefDef(Lc,Eqn) where Eqn matches isEquation(_,Lhs,isMemoAst(_,Rhs))

  ptn isPtnDef(Lc,Eqns) from asApply(Lc,asName(_,"ptn"),asTuple(_,_,list of [Eqns]))

  ptn isPttrnRule(Lc,Lhs,Rhs) from asApply(Lc,asName(_,"from"),asTuple(_,_,list of [Lhs,Rhs]))

  ptn isPrcDef(Lc,Rules) from asApply(Lc,asName(_,"prc"),asTuple(_,_,list of [Rules]))

  ptn isActionRule(Lc,Lhs,Rhs) from asApply(Lc,asName(_,"do"),asTuple(_,_,list of [Lhs,Rhs]))

  ptn isDefDef(Lc,Eqn) from asApply(Lc,asName(_,"def"),asTuple(_,_,[Eqn]))

  ptn isVarDef(Lc,Eqn) from asApply(Lc,asName(_,"var"),asTuple(_,_,[Eqn]))

  ptn isContractDef(Lc,Tp,Body) from asApply(Lc,asName(_,"contract"),
                                        asTuple(_,_,[asApply(_,asName(_,"is"),asTuple(_,"()",[Tp,Body]))]))

  fun definedContractName(isContractDef(_,asApply(_,asName(_,"over"),asTuple(_,"()",[L,R])),_)) is typeName(L)

  ptn isImplementation(Lc,Tp,Exp) from asApply(Lc,asName(_,"implementation"),
                                        asTuple(_,_,[asApply(_,asName(_,"is"),asTuple(_,"()",[Tp,Exp]))]))

  fun implementedContractName(isImplementation(_,asApply(_,asName(_,"over"),asTuple(_,"()",[L,R])),_)) is typeName(L)

  ptn isEqual(Lc,Lhs,Rhs) from asApply(Lc,asName(_,"="),asTuple(_,_,list of [Lhs,Rhs]))

  ptn isEquation(Lc,Lhs,Rhs) from asApply(Lc,asName(_,"is"),asTuple(_,_,list of [Lhs,Rhs]))

  ptn isAssignment(Lc,Lhs,Rhs) from asApply(Lc,asName(_,":="),asTuple(_,_,list of [Lhs,Rhs]))

  ptn isTypeDef(Lc,Rl) from asApply(Lc,asName(_,"type"),asTuple(_,_,list of [Rl]))

  ptn isTypeAliasDef(Lc,Lhs,Rhs) from isTypeDef(Lc,isEquation(_,Lhs,isUnary(_,"alias of",Rhs)))

  ptn isAlgebraicTypeDef(Lc,Lhs,Rhs) from isTypeDef(Lc,isEquation(_,Lhs,Rhs))

  ptn isTypeAssignment(Lc,Nm,Rhs) from asApply(Lc,asName(_,"type"),asTuple(_,"()",[asApply(_,asName(_,"="),asTuple(_,_,[isIden(_,Nm),Rhs]))]))

  ptn isTypeAnnotation(Lc,Lhs,Tp) from asApply(Lc,asName(_,"has type"),asTuple(_,"()",[Lhs,Tp]))

  ptn isKindAnnotation(Lc,Lhs,Tp) from asApply(Lc,asName(_,"has kind"),asTuple(_,"()",[Lhs,Tp]))

  ptn isDefault(Lc,Trm) from asApply(Lc,asName(_,"default"),asTuple(_,"()",[Trm]))

  ptn isDefaultField(Lc,Lhs,Exp) from asApply(Lc,asName(_,"is"),asTuple(_,"()",[isDefault(_,Lhs),Exp]))
   |  isDefaultField(Lc,Lhs,Exp) from asApply(Lc,asName(_,":="),asTuple(_,"()",[isDefault(_,Lhs),Exp]))

  ptn isDefaultFun(Lc,Fun) from isFunDef(Lc,Fun) where Fun matches isEquation(_,isDefault(_,_),_)
                              
  ptn isIden(Lc,Nm) from asName(Lc,Nm)
   |  isIden(Lc,Nm) from asTuple(Lc,"()",list of [asName(_,Nm)])

  ptn isLabeledRecord(Lc,Op,Content) from asApply(Lc,Op,asTuple(_,"{}",Content))

  ptn isFieldAccess(Lc,Lhs,Rhs) from asApply(Lc,asName(_,"."),asTuple(_,_,list of [Lhs,Rhs]))

  ptn isSubstitute(Lc,Lhs,Rhs) from asApply(Lc,asName(_,"substitute"),asTuple(_,_,list of [Lhs,Rhs]))

  ptn isLetTerm(Lc,Body,Bound) from isUnary(Lc,"let",isBinary(_,"in",isBlock(_,Body),Bound))

  ptn isUniversalQ(Lc,astFold(pickVar,set of [],",",Vrs),Tp) from
      asApply(Lc,asName(_,"such that"),asTuple(_,"()",list of [asApply(_,asName(_,"for all"),Vrs),Tp]))

  ptn isWherePtn(Lc,Ptn,Cond) from isBinary(Lc,"where",Ptn,Cond)

  private
  fun pickVar(Vars,isIden(_,V)) is add_element(Vars,V)
   |  pickVar(Vars,_) is Vars

  fun deParen(asTuple(Lc,"()",list of [V])) is V
   |  deParen(V) default is V

  fun definedFunName(asApply(_,asName(_,"fun"),asTuple(_,"()",list of [Rls]))) is 
    checkPipe(Rls,equationName)

  fun definedPrcName(asApply(_,asName(_,"prc"),asTuple(_,"()",list of [Rls]))) is 
    checkPipe(Rls,actionRuleName)

  fun definedPtnName(asApply(_,asName(_,"ptn"),asTuple(_,"()",list of [Rls]))) is 
    checkPipe(Rls,pttrnName)

  fun definedDefNames(asApply(_,asName(_,"def"),asTuple(_,"()",[asApply(_,asName(_,"is"),asTuple(_,"()",list of [L,_]))]))) is 
    ptnDefinedVars(L)

  fun definedVarNames(asApply(_,asName(_,"var"),asTuple(_,"()",[asApply(_,asName(_,":="),asTuple(_,"()",list of [L,_]))]))) is 
    ptnDefinedVars(L)

  fun definedTypeName(asApply(Lc,asName(_,"type"),asTuple(_,_,list of [Rhs]))) is typeName(Rhs)

  fun ptnDefinedVars(asApply(_,asName(_,"?"),asTuple(_,"()",list of [isIden(Lc,Vr)]))) is set of [Vr]
   |  ptnDefinedVars(asApply(_,asName(_,"where"),asTuple(_,"()",list of [L,_]))) is ptnDefinedVars(L)
   |  ptnDefinedVars(asApply(_,asName(_,"default"),asTuple(_,"()",list of [L]))) is ptnDefinedVars(L)
   |  ptnDefinedVars(isIden(_,Vr)) is set of [Vr]
   |  ptnDefinedVars(asTuple(_,_,L)) is rightFold((K,S)=>ptnDefinedVars(K) union S,set of [],L)
   |  ptnDefinedVars(asApply(_,_,A)) is ptnDefinedVars(A)
   |  ptnDefinedVars(_) default is set of []

  private
  fun checkPipe(Trm,F) is let{
    fun checkRules(asApply(_,asName(_,"|"),asTuple(_,"()",list of [L,R]))) is
          compareResult(checkRules(L),checkRules(R))
     |  checkRules(T) is F(T)

    fun compareResult(L matching noGood(_,_),_) is L
     |  compareResult(_,R matching noGood(_,_)) is R
     |  compareResult(good(L),good(R)) is L=R ? good(L) : noGood("$L not same as $R",locOf(Trm))

  } in checkRules(Trm)

  private
  fun equationName(isEquation(_,Lhs,Rhs)) is headName(Lhs)
   |  equationName(E) is noGood("$E is not a valid equation",locOf(E))

  private
  fun actionRuleName(isActionRule(_,Lhs,Rhs)) is headName(Lhs)
   |  actionRuleName(E) is noGood("$E is not a valid action rule",locOf(E))

  private
  fun pttrnName(isPttrnRule(_,Lhs,Rhs)) is headName(Lhs)
   |  pttrnName(E) is noGood("$E is not a valid pattern rule",locOf(E))

  private
  fun headName(asApply(Lc,asName(_,"where"),asTuple(_,_,list of [Lhs,Rhs]))) is headName(Lhs)
   |  headName(asApply(Lc,asName(_,"default"),asTuple(_,_,list of [Lhs]))) is headName(Lhs)
   |  headName(isIden(_,Nm)) is good(Nm)
   |  headName(asApply(_,asName(_,Nm),_)) is good(Nm)
   |  headName(T) default is noGood("cannot determine name from $T",locOf(T))

  private
  fun typeName(asApply(_,asName(_,"where"),asTuple(_,_,[Lhs,Rhs]))) is typeName(Lhs)
   |  typeName(asApply(_,asName(_,"is"),asTuple(_,_,[Lhs,Rhs]))) is typeName(Lhs)
   |  typeName(asApply(_,asName(_,"of"),asTuple(_,_,[L,_]))) is typeName(L)
   |  typeName(asApply(_,asName(_,"such that"),asTuple(_,_,[_,R]))) is typeName(R)
   |  typeName(isIden(_,Nm)) is good(Nm)
   |  typeName(T) default is noGood("cannot determine name from $T",locOf(T))

  fun astFold(Fn,Init,Op,Trm) is let{
    fun termFold(St,asApply(_,asName(_,O where O=Op),asTuple(_,"()",[L,R]))) is termFold(termFold(St,L),R)
     |  termFold(St,T) is Fn(St,T)
  } in termFold(Init,Trm)
  
  fun termFold(Fn,Init,Trm) is astFold(Fn,Init,";",Trm)

  fun pipeFold(Fn,Init,Trm) is astFold(Fn,Init,"|",Trm)
}