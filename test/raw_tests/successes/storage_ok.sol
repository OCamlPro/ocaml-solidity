pragma solidity >=0.6.0;
// SPDX-License-Identifier: UNLICENSED

contract C1 {
  int[] x;
  function f() public view {
    int[] storage y = x;
    int z = y[0];
  }
}

contract C2 {
  function f(int[] storage x) internal view {
    int[] storage y = x;
    int z = y[0];
  }
}
