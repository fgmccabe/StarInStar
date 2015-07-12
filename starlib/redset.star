redset is package{
  -- implement some set-like interfaces for sets based on red-black trees

  private import redblack;

  type redset of t is alias of redblack of (t,());

  implementation collections over redblack of (%t,()) determines %t is {
    fun add_element(S,El) is S[with El->()]
    fun remove_element(S,El) is S[without El]
    fun contains_element(S,El) is present S[El]
    fun is_empty(S) is isEmpty(S)
  }

  emptySet has type for all t such that redset of t;
  def emptySet is _nil();
}