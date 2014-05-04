hex is package{
  grabHex(sequence of {';';..L},Id,Hx,Cx) is (cons(Hx as char,Id),L,Cx+1);
  grabHex(sequence of {X;..L},Id,Hx,Cx) where isHexDigit(X) is 
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
}