pairHeap is package{
  -- implement the pair heap structure

  type ordered is ordered{
    t has kind type;
    leq has type (t,t)=>boolean;
    eq has type (t,t)=>boolean;
    gt has type (t,t)=>boolean;
  };

  type priorityQ is priorityQ {
    elem has type ordered;
    heap has kind type;

    empty has type heap;
    isEmpty has type (heap)=>boolean;

    insrt has type (elem.t,heap)=>heap;
    mrg has type (heap,heap)=>heap;

    findMin has type (heap)=>elem.t;
    deleteMin has type (heap)=>heap;
  };

  pairHeap has type (ordered)=>priorityQ;
  pairHeap(O) is priorityQ{
    elem is O;
    private type heapQ is emptyHeap or T(elem.t,list of heapQ);
    type heapQ counts as heap;

    empty is emptyHeap;
    isEmpty(emptyHeap) is true;
    isEmpty(_) default is false;

    insrt(x,h) is mrg(T(x,list of {}),h);

    mrg(h,emptyHeap) is h;
    mrg(emptyHeap,h) is h;
    mrg(h1 matching T(x1,hs1),h2 matching T(x2,hs2)) is
	elem.leq(x1,x2) ? T(x1,list of {h2;..hs1}) | T(x2,list of {h1;..hs2})

    private
    mergePairs(list of {}) is emptyHeap;
    mergePairs(list of {H}) is H;
    mergePairs(list of {h1;h2;..H}) is mrg(mrg(h1,h2),mergePairs(H));

    findMin(emptyHeap) is raise "empty";
    findMin(T(x,_)) is x;

    deleteMin(emptyHeap) is raise "empty";
    deleteMin(T(_,hs)) is mergePairs(hs);
  }
}
    
    