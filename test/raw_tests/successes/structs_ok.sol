pragma solidity >=0.6.0;

struct s1 {
  s2 x;
}

struct s2 {
  s1[] y;
  mapping(int => int) m;
}

contract C {

  function f(s2 storage s) internal view {

  }

}
