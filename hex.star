hex is package{
  fun grabHex([0c;,..L],Id,Hx,Cx) is (cons(Hx,Id),L,Cx+1)
   |  grabHex([X,..L],Id,Hx,Cx) where isHexDigit(X) is 
        grabHex(L,Id,Hx*16+hexDigitVal(X),Cx+1)
   |  grabHex(L,Id,Hx,Cx) is (cons(Hx,Id),L,Cx)

  fun isHexDigit(X) is (0c0=<X and X=<0c9) or (0ca=<X and X=<0cf) or (0cA=<X and X=<0cF)

  private
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
  
  fun hexDigitVal(X) where 0c0=<X and X=<0c9 is X-0c0
   |  hexDigitVal(X) where 0ca=<X and X=<0cf is X-0ca+10
   |  hexDigitVal(X) where 0cA=<X and X=<0cF is X-0cA+10
}