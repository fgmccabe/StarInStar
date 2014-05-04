errors is package{
  import location;
  private type errorMsg is errorMsg(string,list of srcLoc);

  private errorActor is actor{
    errors has type ref list of errorMsg;
    var errors := list of {};

    on Msg on error do
      extend errors with Msg;

    reportAllErrors() do {
      if not isEmpty(errors) then {
	logMsg(warning,"errors and warnings:");
	for errorMsg(Msg,Lc) in errors do
	    logMsg(warning,display(Lc),Msg);
      }
      else
      logMsg(info,"No errors or warnings");
    };
  };

  reportAllErrors() do
    request errorActor's reportAllErrors to reportAllErrors();

  reportError(Msg,Locs) do {
    logMsg(info,"Error: $Msg at $Locs");
    notify errorActor with errorMsg(Msg,Locs) on error;
  }

  isErrorFree() is noNewErrors(0);

  errorCount() is query errorActor's errors with size(errors);

  noNewErrors(mark) is query errorActor's errors with size(errors)=mark;
}