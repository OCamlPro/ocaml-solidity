contract C {
  enum e { a, b } // encodé comme un uint8 en interne
  function f(uint8 x) public {}
  function f(e x) public {}
}