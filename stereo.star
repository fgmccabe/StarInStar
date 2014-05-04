stereo is package{
  val(0,0) is match(0,0);
  val(i,j) where i>0 and j>0 is valof{
    iL is i-1;
    jL is j-1;
		
    valis max(val(iL,jL)+match(i,j), max(val(iL,j)+occ, val(i,jL)+occ))
  };
  val(0,j) where j>0 is 
      val(0,j-1)+occ;
  val(i,0) is val(i-1,0)+occ;
	
  occ is 10;
	
  match(i,j) where i>=0 and j>=0 and i<size(L) and j<size(R) is comp(L[i],R[j]);
  match(i,j) default is 20;
	
  comp(X,X) is 0;
  comp(X,Y) where X!=Y is 20;
	
  L is list of {black; red; black; black; black};
  R is list of {black; black; black; red; black};
  
  type color is red or black;
  
  main()
  {
    logMsg(info,"result is $(val(5,5))");
  }
}