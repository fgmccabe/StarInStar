fact is package{
	fact has type (integer,integer)=>integer

	fun fact(0) is 1
	 |  fact(N) is N*fact(N-1)
}