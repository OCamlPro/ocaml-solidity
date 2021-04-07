contract C1 {
  function f(string memory x) public virtual {}
}
contract C2 is C1 {
  function f(int x) public override {}
}