contract C {
  int[] a;

  function pop() public view { /* pure/view forbidden... */
    a.pop();
  }

}