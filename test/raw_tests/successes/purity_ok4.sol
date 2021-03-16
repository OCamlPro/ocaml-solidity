contract C {
   int x;
   modifier M() { x = 42; _; }
   function f() public M {}
}