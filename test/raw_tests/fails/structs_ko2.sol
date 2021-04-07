pragma solidity >=0.6.0;

struct s1 {
  s2 x;
}

struct s2 {
  mapping(int => int) m;
}

contract C {

  function f(s1 memory s) public view {

  }

}
