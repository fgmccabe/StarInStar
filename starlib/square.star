square is package{
  private import folding;
  -- refactored from the Go! implementation

  contract square over t determines e is {
    column has type (t,integer)=>list of e;
    row has type (t,integer)=>list of e;
    quad has tyoe (t,integer)=>list of e;
    cell has type (t,integer,integer)=>e;

    setCell has type (t,integer,integer,e)=>t;
  }

  type intSquare is intSquare(integer,array of integer);

  implementation square over intSquare determines integer is {
    column(intSquare(Sx,L),Cx) is everyIth(L,Sx,Cx);
    row(intSquare(Sx,L),Rx) is L[Sx*Rx:Sx*(Rx+1)];

    quad(intSquare(Sx,L),Qx) is let{
      -- index of first element of quadrant Qx
      Ix is ((Qx-1)/Sx)*Sx*Sx*Sx+((Qx-1)%Sx)*Sx;

      qdOf(_,0) is list of {};
      qdOf(Els,Cnt) is Els[0:Sx]++qdOf(Els[Sx:],Cnt-1);
    } in qdOf(L[Ix:],Sx)

    private
    everyIth(L,Sx,Cx) where size(L)<Cx is list of {};
    everyIth(L,Sx,Cx) is list of {L[Cx];..everyIth(L[Sx:],Sx,Cx)};

    cell(intSquare(Sx,L),Ix,Iy) is L[Sx*Ix+Iy];

    setCell(intSquare(Sx,L),Ix,Iy,V) is 
	intSquare(Sx,_set_indexed(L,Sx*Ix+Iy,V));
  }


    