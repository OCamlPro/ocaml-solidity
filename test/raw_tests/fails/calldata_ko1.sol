pragma solidity >=0.6.0;
// SPDX-License-Identifier: UNLICENSED

contract C {
  function f(int[] calldata x) external pure {
    int[] calldata y;
    int z = y[0];
  }
}

/*
Error: This variable is of calldata pointer type and can be accessed without prior assignment, which would lead to undefined behaviour.
*/
