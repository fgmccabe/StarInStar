redset is package{
  -- implement some set-like interfaces for sets based on red-black trees

  private import redblack;

  type redset of t is alias of redblack of (t,());

  implementation collections over redblack of (%t,()) determines %t is {
    add_element(S,El) is S[with El->()];
    remove_element(S,El) is S[without El];
    contains_element(S,El) is present S[El];
    is_empty(S) is isEmpty(S);
  }

  emptySet has type for all t such that redset of t;
  emptySet is _nil();
}