dependencies is package{
  private import topsort
  private import ast
  private import good
  private import astUtils
  private import access
  private import (trace)

  -- name spaces
  type category is expsion or tipe or other
  type astGroup is alias of list of ((ast, accessMode, category,set of string))

  dependencies has type (list of ast) => list of astGroup
  fun dependencies(Th) is let{
    def definitions is programDefs(Th)
    def groups is topological(definitions) trace "groups"
    fun projectCat(D) is someValue(any of C where (C,_) in D)
    fun projectDefs(D) is set of {all Df where (_,Df) in D}
  } in (list of { all list of {all (T,A,projectCat(D),projectDefs(D)) where topDef{orig=(A,T);definitions=D} in group} where group in groups})

  private
  programDefs has type (list of ast) => list of topDef of ((accessMode,ast),(category,string))
  fun programDefs(L) is let{
    def Dfs is map((S)=>definitionStruct(S,pUblic),L)
    def All is buildDefDict(Dfs)
  } in map(((Fn,A,_,Defs,Trm))=>topDef{orig=(A,Trm);definitions=Defs;references = Fn(Trm,All,set of [])},Dfs)

  private
  fun definitionStruct(D,A) is switch D in {
    case isUnary(_,"private",Def) is definitionStruct(Def,priVate)
    case asApply(_,asName(_,"type"),_) is (analyseTypeDefn,A,tipe,setOfGood(definedTypeName(D),tipe),D)
    case asApply(_,asName(_,"fun"),_) is (analyseFunDefn,A,expsion,setOfGood(definedFunName(D),expsion),D)
    case asApply(_,asName(_,"prc"),_) is (analysePrcDefn,A,expsion,setOfGood(definedPrcName(D),expsion),D)
    case asApply(_,asName(_,"ptn"),_) is (analysePtnDefn,A,expsion,setOfGood(definedPtnName(D),expsion),D)
    case asApply(_,asName(_,"def"),_) is (analyseDefDefn,A,expsion,map((Nm)=>(expsion,Nm),definedDefNames(D)),D)
    case asApply(_,asName(_,"var"),_) is (analyseVarDefn,A,expsion,map((Nm)=>(expsion,Nm),definedVarNames(D)),D)
    case asApply(_,asName(_,"contract"),_) is (analyseContract,A,tipe,setOfGood(definedContractName(D),tipe),D)
    case asApply(_,asName(_,"implementation"),_) is (analyseImplementation,A,expsion,setOfGood(implementedContractName(D),expsion),D)
    case asApply(_,asName(_,"import"),_) is (analyseImport,A,other,set of [],D)
    case asApply(_,asName(_,"is"),asTuple(_,"()",[_,asApply(_,asName(_,"import"),_)])) is (analyseImport,A,other,set of [],D)
    case X default is (analyseOther,A,other,set of [],D)
  }

  private
  fun buildDefDict(L) is leftFold((Dc,E)=>refDict(E,Dc),dictionary of [],L)

  private
  fun refDict((_,_,k,N,_),D) where D[k] has value Defs is D[with k->Defs union N]
   |  refDict((_,_,k,N,_),D) default is D[with k->N]

  private
  analyseTypeDefn has type (ast,dictionary of (category,set of ((category,string))),set of ((category,string)))=>set of ((category,string))
  fun analyseTypeDefn(asApply(_,asName(_,"type"),asTuple(_,_,[Rhs])),All,Excl) is switch Rhs in {
        case asApply(_,asName(_,"counts as"),SS) is findRefs(SS,tipe,All,set of [],Excl)
        case asApply(_,asName(_,"is"),asTuple(_,"()",[L,asApply(_,asName(_,"of"),asTuple(_,_,[asName(_,"alias"),R]))])) is 
              findRefs(R,tipe,All,set of [],Excl)
        case asApply(_,asName(_,"is"),asTuple(_,"()",[L,R])) is findConstructorRefs(R,set of [],All,Excl)
  }

  private
  fun findConstructorRefs(Tp,Refs,All,Excl) is astFold((Rfs,Trm)=>analyseConstructor(Trm,Rfs,All,Excl),Refs,"or",Tp)

  private
  fun analyseConstructor(asName(_,_),Refs,All,Excl) is Refs
   |  analyseConstructor(asApply(_,asName(_,_),Tpl matching asTuple(_,"()",_)),Refs,All,Excl) is findRefs(Tpl,tipe,All,Refs,Excl)
   |  analyseConstructor(asApply(_,asName(_,_),asTuple(_,"{}",Body)),Refs,All,Excl) is valof{
        def excludes is leftFold(excludeName,Excl,Body)
        valis leftFold((Rfs,Stmt)=>analyseAnnotation(Stmt,Rfs,All,excludes),Refs,Body)
      }

  private
  fun excludeName(Excl,isTypeAnnotation(_,isIden(_,Nm),_)) is add_element(Excl,((expsion,Nm)))
   |  excludeName(Excl,isKindAnnotation(_,isIden(_,Nm),_)) is add_element(Excl,((tipe,Nm)))
   |  excludeName(Excl,_) default is Excl

  private
  fun analyseAnnotation(isTypeAnnotation(_,_,Tp),Refs,All,Excl) is findRefs(Tp,tipe,All,Refs,Excl)
   |  analyseAnnotation(isDefaultField(_,_,Exp),Refs,All,Excl) is findRefs(Exp,expsion,All,Refs,Excl)
   |  analyseAnnotation(isDefaultFun(_,Eqn),Refs,All,Excl) is analyseEquation(Eqn,Refs,All,Excl)
   |  analyseAnnotation(Trm,Refs,_,_) default is Refs


  private
  fun analyseFunDefn(isFunDef(_,Eqns),All,Excl) is 
        pipeFold((Refs,Eqn)=>analyseEquation(Eqn,Refs,All,Excl),set of [],Eqns)

  private
  fun analyseEquation(isEquation(_,Lhs,Rhs),Refs,All,Excl) is findRefs(Rhs,expsion,All,findRefs(Lhs,expsion,All,Refs,Excl),Excl)

  private
  fun analysePrcDefn(isPrcDef(_,Rules),All,Excl) is
        pipeFold((Refs,Rle)=>analyseActionRule(Rle,Refs,All,Excl),set of [],Rules)

  private
  fun analyseActionRule(isActionRule(_,Lhs,Rhs),Refs,All,Excl) is findRefs(Rhs,expsion,All,findRefs(Lhs,expsion,All,Refs,Excl),Excl)

  private
  fun analysePtnDefn(isPtnDef(_,Rules),All,Excl) is
        pipeFold((Refs,Rle)=>analysePttrnRule(Rle,Refs,All,Excl),set of [],Rules)

  private
  fun analysePttrnRule(isPttrnRule(_,Lhs,Rhs),Refs,All,Excl) is findRefs(Lhs,expsion,All,findRefs(Rhs,expsion,All,Refs,Excl),Excl)

  private
  fun analyseDefDefn(isDefDef(_,isEquation(_,Lhs,Rhs)),All,Excl) is 
    findRefs(Rhs,expsion,All,findRefs(Lhs,expsion,All,set of [],Excl),Excl)

  private
  fun analyseVarDefn(isVarDef(_,isAssignment(_,Lhs,Rhs)),All,Excl) is 
    findRefs(Rhs,expsion,All,findRefs(Lhs,expsion,All,set of [],Excl),Excl)

  private
  fun analyseContract(isContractDef(_,_,conType,conBody),All,Excl) is
    findRefs(conBody,tipe,All,findRefs(conType,tipe,All,set of [],Excl),Excl)

  private
  fun analyseImplementation(isImplementation(_,Tp,Exp),All,Excl) is
    findRefs(Exp,expsion,All,findRefs(Tp,tipe,All,set of [],Excl),Excl)

  private
  fun analyseImport(Trm,All,Excl) is set of []

  private
  fun analyseOther(Trm,All,Excl) is findRefs(Trm,expsion,All,set of [],Excl)

  private
  fun findRefs(Trm,Mode,All,soFr,Excl) is let{
    fun fndRefs(asName(_,Nm),ky,soFar) where not (ky,Nm) in Excl and 
          All[ky] has value Defs and (ky,Nm) in Defs is set of [(ky,Nm),..soFar]
   |  fndRefs(asName(_,Nm), expsion, soFar) is soFar
   |  fndRefs(asApply(Lc,asName(_,"where"),asTuple(_,_,list of [Lhs,Rhs])),expsion,soFar) is 
        fndRefs(Lhs,expsion,fndRefs(Rhs,expsion,soFar))
   |  fndRefs(asApply(Lc,asName(_,"default"),asTuple(_,_,[Lhs])),expsion,soFar) is 
        fndRefs(Lhs,expsion,fndRefs(Lhs,expsion,soFar))
   |  fndRefs(asApply(Lc,asName(_,"has type"),asTuple(_,_,list of [Lhs,Rhs])),cat,soFar) is 
        fndRefs(Lhs,cat,fndRefs(Rhs,tipe,soFar))
   |  fndRefs(asApply(_,O,A),sK,soFar) is fndRefs(A,sK,fndRefs(O,sK,soFar))
   |  fndRefs(asTuple(_,_,L),sK,soFar) is leftFold((soF,E)=>fndRefs(E,sK,soF),soFar,L)
   |  fndRefs(_,_,soFar) default is soFar
  } in fndRefs(Trm,Mode,soFr)
  
  private
  fun setOfGood(good(K),Mode) is set of [(Mode,K)]
   |  setOfGood(_,_) is set of []
}