collections is package{
  contract collections over t determines e is {
    emptySet has type t;
    add_element has type (t,e)=>t;
    remove_element has type (t,e)=>t;
    contains_element has type (t,e)=>boolean;
  }

}
  