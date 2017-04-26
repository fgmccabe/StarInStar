access is package{
  type accessMode is priVate or pUblic

  implementation pPrint over accessMode is {
    fun ppDisp(priVate) is ppStr("private ")
     |  ppDisp(pUblic) is ppStr("public")
  }
}