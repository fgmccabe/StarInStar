errors is package{
  import location
  private type errorMsg is errorMsg(string,list of srcLoc)

  private def errorActor is actor{
    errors has type ref list of errorMsg
    var errors := list of [];

    on Msg on error do
      extend errors with Msg

    prc reportAllErrors() do {
      if not isEmpty(errors) then {
        logMsg(warning,"errors and warnings:")
        for errorMsg(Msg,Lc) in errors do
          logMsg(warning,display(Lc),Msg)
      }
      else
        logMsg(info,"No errors or warnings")
    }
  }

  prc reportAllErrors() do
    request errorActor's reportAllErrors to reportAllErrors()

  prc reportError(Msg,Locs) do {
    logMsg(info,"Error: #Msg at $Locs")
    notify errorActor with errorMsg(Msg,Locs) on error
  }

  fun isErrorFree() is noNewErrors(0)

  fun errorCount() is query errorActor's errors with size(errors)

  fun noNewErrors(mark) is query errorActor's errors with size(errors)=mark
}