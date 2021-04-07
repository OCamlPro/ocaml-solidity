contract C {
  int[] a;
  function f() public view { /* pure/view forbidden */
    a.pop;
  }
}