topsort is package{

  type topDef of (o,t) where equality over t and equality over o is topDef{
    orig has type o
    definitions has type set of t
    references has type set of t
  }

  topological has type for all o,t such that 
    (list of topDef of (o,t))=>list of list of topDef of (o,t) where pPrint over t and pPrint over o
  fun topological(definitions) is let{

    type defEntry is  dE{
      df has type topDef of (o,t)
      stackRef has type ref option of integer
    }

    var stack := list of []
    def defs is list of { all dE{ df = d; stackRef := none} where d in definitions }
    var groups := list of []
    def index is buildIndex(defs)

    analyseDef has type (defEntry)=>integer
    fun analyseDef(D) is valof {
      def low is push(D)
      def point is analyseRefs(D.df.references,low)

      if point = low then { -- we have a group
        var group := list of []
        while stack matches [Top,..Rest] and Top.stackRef has value off and off>= point do {
          group := [Top.df,..group]
          stack := Rest
        }
        if not isEmpty(group) then
          groups := [groups..,group]
      }
      valis point
    }

    fun sort() is valof{
      for D in defs do {
        if D.stackRef=none then
          ignore analyseDef(D)
      }
      valis groups
    }

    fun analyseRefs(refs,point) is valof {
      var low := point
      for rf in refs do {
        low := minPoint(low,analyse(rf,low))
      }
      valis low
    }

    fun analyse(rf,low) is valof{
      for D in stack do {
        if rf in D.df.definitions and D.stackRef has value R then
          valis minPoint(R,low)
      }

      if findDef(rf) has value df then
        valis minPoint(low,analyseDef(df))
      else
        valis low
    }

    fun minPoint(x,y) where x=<y is x
     |  minPoint(_,y) default is y

    fun push(D) is valof{
      def count is size(stack)
      D.stackRef := some(count)
      stack := [D,..stack]
      valis count
    }

    buildIndex has type (list of defEntry)=>dictionary of (t,list of defEntry)
    fun buildIndex(Defs) is valof{
      var Index := dictionary of []
      for Ix->D in Defs do {
        for d in D.df.definitions do {
          if Index[d] has value links then
            Index[d] := [D,..links]
          else
            Index[d] := [D]
        }        
      }
      valis Index
    }

    fun findDef(Ky) where index[Ky] has value L and D in L and  D.stackRef=none is some(D)
     |  findDef(_) default is none
  } in sort()
}