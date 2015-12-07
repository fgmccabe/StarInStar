nogood is package{

  type good of (T,E) is good(T) or noGood(E)

  implementation for all T,E such that pPrint over good of (T,E) where pPrint over T and pPrint over E is {
    ppDisp=showGood
  } using {
    fun showGood(good(G)) is ppSequence(0,[ppStr("good"),ppSpace,ppDisp(G)])
     |  showGood(noGood(N)) is ppSequence(0,[ppStr("noGood"),ppSpace,ppDisp(N)])
  }
  
  fun more(good(G),F) is F(G)
   |  more(noGood(M),F) is noGood(M)
}