contract D {
}

contract C {
  function f() public pure { /* pure/view forbidden */
    D d = new D();
  }
}