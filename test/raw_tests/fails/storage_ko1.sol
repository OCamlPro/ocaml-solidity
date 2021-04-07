pragma solidity >=0.6.0;
// SPDX-License-Identifier: UNLICENSED

contract C {
  int[] x;
  function f() public view {
    int[] storage y;
    int z = y[0];
  }
}

/*
Error: This variable is of storage pointer type and can be accessed without prior assignment, which would lead to undefined behaviour.
*/
