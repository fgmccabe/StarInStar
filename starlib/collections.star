collections is package{
  contract collections over t determines e is {
    emptySet has type t;
    add_element has type (t,e)=>t;
    remove_element has type (t,e)=>t;
    contains_element has type (t,e)=>boolean;
  }

  type set of %t is alias of dictionary of (%t,());

  implementation for all k such that collections over dictionary of (k,()) determines k is {
    emptySet is dictionary of {};
    add_element(S,K) is S[with K->()]
    remove_element(S,K) is S[without K]
    contains_element(S,K) is present S[K];
  }
}
  