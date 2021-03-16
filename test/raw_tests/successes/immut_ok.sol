pragma solidity >=0.6.0;
// SPDX-License-Identifier: UNLICENSED

contract C1 {
  int immutable x = 42;
}

contract C2 {
  constructor() public { x = 42; }
  int immutable x;
}
