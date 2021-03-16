contract C {
  int[] a;

  function pop() public pure {
    (true ? a.pop : a.pop)();
  }

}