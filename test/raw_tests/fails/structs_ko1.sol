pragma solidity >=0.6.0;

struct s1 {
  s2 x;
}

struct s2 {
  s1[] y;
}

contract C {

  function f(s2 memory s) public view {

  }

}
