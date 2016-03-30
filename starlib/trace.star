trace is package{
  #infix("trace",999)

  fun X trace M is valof{
    logMsg(info,M++": $X")
    valis X
  }
}