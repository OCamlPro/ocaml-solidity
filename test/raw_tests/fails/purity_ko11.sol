contract D {
}

contract C {
  function f() public view { /* pure/view forbidden */
    D d = new D();
  }
}