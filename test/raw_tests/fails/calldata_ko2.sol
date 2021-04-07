pragma solidity >=0.6.0;
// SPDX-License-Identifier: UNLICENSED

contract C {
  function f(int[] calldata x) external pure {
    int[] calldata y = x;
    y[0] = 42;
  }
}

/*
Error: Calldata arrays are read-only.
*/
