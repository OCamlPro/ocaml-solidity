pragma solidity >=0.6.0;
// SPDX-License-Identifier: UNLICENSED

contract C1 {
  int immutable x = 42;
}

contract C2 is C1 {
  constructor() public { x = 42; }
}

/*
Error: Immutable variables must be initialized in the constructor of the contract they are defined in.
*/
