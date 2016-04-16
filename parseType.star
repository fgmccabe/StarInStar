parseType is package{
  private import ast
  private import astUtils
  private import canonical
  private import types
  private import location
  private import freshen
  private import subsume
  private import good
  private import (trace)

  fun parseType(Ast,Dict) is typeParse(Ast,Dict,dictionary of [])

  fun typeParse(Ast,Dict,BndVars) is let {
    fun parseTp(asName(_,Nm)) where BndVars[Nm] has value Tp is good(Tp)
     |  parseTp(asName(Lc,Nm)) where findType(Dict,Nm) has value Desc is
          switch Desc in {
            case typeIs{tipe=Tpe} is good(freshen(Tpe))
            case algebraicEntry{tipe=Tpe} is good(freshen(Tpe))
       --     case typeAlias(A) where A(iType(Nm)) has value Tp is good(Tp)
            case _ default is noGood("cannot understand type $Nm",Lc)
          }
     |  parseTp(asTuple(_,"()",L)) is 
          more(goodIterate(L,parseTp),(lt)=>good(iTuple(lt)))
     |  parseTp(R matching asTuple(_,"{}",Els)) is parseRecordType(R,Dict,BndVars)
     |  parseTp(isBinary(Lc,"of",L,R)) is 
          more(parseTp(R), (At)=>more(parseTp(L),(Ft)=>checkTypeExp(Ft,At,Lc)))
     |  parseTp(isBinary(_,"=>",L,R)) is 
          more(parseTp(L),(At)=>more(parseTp(R),(Ft)=>good(iFnTp(At,Ft))))
     |  parseTp(isBinary(_,"<=",L,R)) is 
          more(parseTp(L),(At)=>more(parseTp(R),(Ft)=>good(iPtTp(At,Ft))))
     |  parseTp(isBinary(_,"<=>",L,R)) is 
          more(parseTp(L),(At)=>more(parseTp(R),(Ft)=>good(iConTp(At,Ft))))
     |  parseTp(isUnary(_,"ref",R)) is 
          more(parseTp(deParen(R)),(Rt)=>good(iRfTp(Rt))) 
     |  parseTp(T) where isUniv(T) has value (bVs,R) is valof{
          def M1 is leftFold((m,v) => m[with v->iBvar(v)],BndVars,bVs)

          switch typeParse(R,Dict,M1) in {
            case good(Bt) do
              valis good(leftFold((t,v)=>iUniv(v,t),Bt,bVs))
            case noGood(M,mLc) do
              valis noGood(M,mLc)
          }
        }
     |  parseTp(T) where isExists(T) has value (bVs,R) is valof{
          def M1 is leftFold((m,v) => m[with v->iBvar(v)],BndVars,bVs)

          switch typeParse(R,Dict,M1) in {
            case good(Bt) do
              valis good(leftFold((t,v)=>iExists(v,t),Bt,bVs))
            case noGood(M,mLc) do
              valis noGood(M,mLc)
          }
        }
     |  parseTp(isBinary(_,"where",L,R)) is more(parseTp(L),(Tp)=>parseConstraints(R,Tp))
     |  parseTp(T) default is 
          noGood("cannot understand type expression $(T)",locOf(T))

    fun checkTypeExp(iTpExp(F,A),B,Lc) is switch subsume(Dict,Lc)(A,B) in {
          case good(_) is good(iTpExp(F,A))
          case noGood(E,_) is noGood("$(iTpExp(F,A)) is not applicable to $B\nbecause $E",Lc)
        }
     | checkTypeExp(Tp,B,Lc) is noGood("$Tp does not apply to $B",Lc)

    fun parseConstraints(isBinary(_,"and",L,R),T) is more(parseConstraints(L,T),(Tp)=>parseConstraints(R,Tp))
     |  parseConstraints(isBinary(_,"over",L,isBinary(_,"determines",A,D)),T) where 
          isName(L) has value Ct is 
          more(parseTpArgs(A,Dict,BndVars),(At)=>more(parseTpArgs(D,Dict,BndVars),(Dt)=>good(iConstrained(T,isOver(iContract(Ct,At,Dt))))))
     |  parseConstraints(isBinary(_,"over",L,R),T) where 
          isName(L) has value Ct is 
          more(parseTpArgs(L,Dict,BndVars),(At)=>more(parseTpArgs(R,Dict,BndVars),(Dt)=>good(iConstrained(T,isOver(iContract(Ct,At,[]))))))
     |  parseConstraints(isBinary(_,"instance of",L,R),T) is
          more(parseTp(L),(Lt)=>more(parseTp(R),(Rt)=>good(iConstrained(T,instanceOf(Lt,Rt)))))
     |  parseConstraints(isBinary(_,"implements",L,asTuple(_,"{}",Ls)),T) is valof{
          switch parseTp(L) in {
            case good(t) do {
              var ts := T
              for El in Ls do{
                if El matches isBinary(_,"has type",isIden(_,F),FT) then {
                  switch parseTp(FT) in {
                    case good(ft) do 
                      ts := iConstrained(ts,hasField(t,F,ft))
                    case noGood(M,mLc) do
                      valis noGood(M,mLc)
                  }
                }
                else if El matches isBinary(_,"has kind",asName(_,F),FK) then{
                  switch parseKind(FK) in {
                    case good(K) do
                      ts := iConstrained(ts,iFieldKind(t,F,K))
                    case noGood(eM,eLc) do
                      valis noGood(eM,eLc)
                  }
                }
              }
              valis good(ts)
            }
            case noGood(eM,eLc) do
              valis noGood(eM,eLc)
          }
        }
     |  parseConstraints(isBinary(_,"has kind",L,R),T) is 
          more(parseTp(L),(lt)=>more(parseKind(R),(K)=>good(iConstrained(T,hasKind(lt,K)))))

  } in parseTp(Ast)

  private
  fun parseTpArgs(asTuple(_,"()",L),D,Q) is goodIterate(L,(E)=>typeParse(E,D,Q))
   |  parseTpArgs(T,D,Q) is goodSequence(list of [typeParse(T,D,Q)])


  private
  fun parseKind(asName(_,"type")) is good(kType)
   |  parseKind(isBinary(_,"of",asName(_,"type"),R)) is good(kTypeFun(countTypes(R)))
   |  parseKind(asName(_,"unknown")) is good(kUnknown)
   |  parseKind(A) is noGood("Invalid kind specification $A",locOf(A))

  private
  fun countTypes(asName(_,"type")) is 1
   |  countTypes(asTuple(_,"()",L)) is size(L)

  private
  parseRecordType has type (ast,dict,dictionary of (string,iType))=>good of iType
  fun parseRecordType(asTuple(_,"{}",Els),Dict,BndVars) is valof{
    var fields := dictionary of []
    var types := dictionary of []
    var exVars := list of []

    for St in Els do{
      switch St in {
        case isBinary(_,"has type",L,R) do {
          if deParen(L) matches asName(Lc,Id) then{
            switch typeParse(R,Dict,BndVars) in {
              case good(T) do
                fields[Id] := T
              case noGood(M,mLc) do
                valis noGood(M,mLc)
            }
          }
          else
            valis noGood("Field $L should be an identifier",locOf(L))
        }
        case isBinary(_,"has kind",L,R) do {
          if deParen(L) matches asName(_,Id) then {
            def eType is iBvar(Id)
            switch parseKind(R) in {
              case good(K) do {
                exVars := list of [hasKind(eType,K),..exVars]
                types[Id] := eType
              }
              case noGood(M,eLc) do
                valis noGood(M,eLc)
            }
          }
          else
            valis noGood("Field $L should be an identifier",locOf(L))
        }
        case isUnary(_,"type",isBinary(_,"=",Lhs,Rhs)) do {
          if deParen(Lhs) matches asName(_,Id) then {
            switch typeParse(Rhs,Dict,BndVars) in {
              case good(T) do
                types[Id] := T
              case noGood(M,mLc) do
                valis noGood(M,mLc)
            }
          }
          else
            valis noGood("Field $Lhs should be an identifier",locOf(Lhs))
        }
        case _ default do 
          valis noGood("Invalid element $St in record type",locOf(St))
      }
    }
    var reslt := iFace(fields,types)
    for HK in exVars do 
      reslt := iConstrained(reslt,HK)
    
    for hasKind(iBvar(tv),_) in exVars and not present BndVars[tv] do 
      reslt := iExists(tv,reslt)
  
    valis good(reslt)
  }

  fun introduceContract(isContractDef(Lc,CNm,Spec,Body),D) is good computation {
    def TQ is valof contractSpecVars(Spec,dictionary of [])
    def (Nm,contrct) is valof parseContractSpec(Spec,D,TQ)
    def body is valof parseRecordType(Body,D,TQ)
    def entry is contractEntry{loc=Lc;tipe=contrct;spec=rebind(iTuple([contrct,body]),TQ)}
    var Dict := D substitute { contracts = D.contracts[with Nm->entry]}

    if body matches iFace(Fields,Types) then {
      for K->T in Fields do 
        Dict := defineVar(Dict,Lc,K,rebind(iConstrained(T,isOver(contrct)),TQ))
    }

    valis Dict
  }

  private
  fun rebind(Tp,Q) is rightFold(((K,_),T)=>iUniv(K,T),Tp,Q)

  private
  fun pushInQuants(iFace(Fields,Types),Q,Fn) is iFace(rightFold(((K,KT),F)=>F[with K->rebind(Fn(KT),Q)],dictionary of [],Fields),Types)
   |  pushInQuants(Tp,Q,Fn) default is rebind(Fn(Tp),Q)

  private
  fun contractSpecVars(C,Q) is let {
    fun contractVars(isBinary(_,"over",_,isBinary(_,"determines",A,T))) is 
          more(collectCommaVars(A,Q),(QQ)=>collectCommaVars(T,QQ))
     |  contractVars(isBinary(_,"over",_,A)) is collectCommaVars(A,Q)

    fun collectCommaVars(isBinary(_,",",L,R),QQ) is 
          more(collectCommaVars(L,QQ),(QQv)=>collectCommaVars(R,QQv))
     |  collectCommaVars(isBinary(_,"where",L,R),QQ) is collectCommaVars(L,QQ)
     |  collectCommaVars(asName(Lc,Nm),QQ) is good(QQ[with Nm->iBvar(Nm)])
     |  collectCommaVars(Ast,QQ) is noGood("$Ast not a valid contract spec",locOf(Ast))
  } in contractVars(C)

  fun parseContractSpec(isBinary(_,"over",asName(_,Ct),isBinary(_,"determines",A,T)),D,Q) is 
        more(parseTpArgs(A,D,Q),(At)=>more(parseTpArgs(T,D,Q),(Dt)=>good((Ct,iContract(Ct,At,Dt)))))
   |  parseContractSpec(isBinary(_,"over",asName(_,Ct),L),D,Q) is 
        more(parseTpArgs(L,D,Q),(At)=>good((Ct,iContract(Ct,At,[]))))
   |  parseContractSpec(Ast,D,Q) is noGood("$Ast not a valid contract specification",locOf(Ast))

  private
  fun typeTemplateVars(isBinary(_,"where",L,C)) is typeTemplateVars(L)
   |  typeTemplateVars(isBinary(_,"of",isIden(_,TNm),asTuple(_,"()",A))) is valof{
        def aT is dictionary of { all Nm->iBvar(Nm) where isIden(_,Nm) in A }

        valis (aT,TNm,iTpExp(iType(TNm),iTuple(list of {all argT where isIden(_,Nm) in A and aT[Nm] has value argT})))
      }
   |  typeTemplateVars(isBinary(_,"of",isIden(_,TNm),isIden(_,Nm))) is valof{
        def aT is iBvar(Nm);
        valis (dictionary of [Nm->aT],TNm,iTpExp(iType(TNm),aT))
      }
   |  typeTemplateVars(isIden(_,TNm)) is (dictionary of [],TNm,iType(TNm))

  private
  fun typeFunVar(Nm,D,Q) where findType(D,Nm) has value _ is Q
   |  typeFunVar(Nm,_,Q) is Q[with Nm->iBvar(Nm)]

  fun typeTemplate(Ast,D) is good computation {
    def (templateVars,TNm,TT) is typeTemplateVars(Ast)
    def template is valof typeParse(Ast,D,templateVars[with TNm->TT])
    valis rebind(template,templateVars)
  }

  fun parseAlgebraicType(isAlgebraicTypeDef(Lc,Nm,Lhs,Rhs),ODict) is good computation{
      def (Q,_,TT) is typeTemplateVars(Lhs)
      def template is valof typeParse(Lhs,ODict,Q[with Nm->TT])

      def Dict is introduceType(ODict,Lc,Nm,rebind(template,Q))
      def conDefs is valof astFold((soF,C)=>more(soF,
                  (sF)=>more(parseConstructor(C,Dict,Q,TT),
                    ((CNm,CLc,Ctp))=>good(list of [(CNm,CLc,rightFold(((K,_),conT)=>iUniv(K,conT),Ctp,Q)),..sF]))),
                  good(list of []),"or",Rhs)
      valis rightFold(((K,CLc,KT),D)=>defineConstructor(D,CLc,K,KT),Dict,conDefs)
    }
   | parseAlgebraicType(Def,ODict) is noGood("cannot parse $Def as algebraicEntry",locOf(Def)) trace "cannot parse $Def"

  fun parseConstructor(asApply(Lc,asName(_,Op),Args),D,Q,Tp) is good computation {
        def argType is valof typeParse(Args,D,Q)
        valis (Op,Lc,iConTp(argType,Tp))
      }
   |  parseConstructor(isIden(Lc,Op),D,Q,Tp) is good((Op,Lc,Tp))
   |  parseConstructor(Ast,_,Q,Tp) is noGood("Cannot understand $Ast as constructor",locOf(Ast))

-- Use this when ast is properly implemented
--  isUniv(<|for all ?V such that ?T |>) is some((V,T))
  private 
  fun isUniv(isBinary(_,"such that",isUnary(_,"for all",V),R)) is some((deComma(V),R))
   |  isUniv(_) default is none

  private
  fun isExists(isBinary(_,"such that",isUnary(_,"for all",V),R)) is some((deComma(V),R))
   |  isExists(_) default is none

  fun deComma(isBinary(_,",",L,R)) is deComma(L)++deComma(R)
   |  deComma(asName(_,Id)) is list of [Id]
}