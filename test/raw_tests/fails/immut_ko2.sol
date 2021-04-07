pragma solidity >=0.6.0;
// SPDX-License-Identifier: UNLICENSED

contract C {
  constructor() public { x = 42; }
  int immutable x = 42;
}

/*
Error: Immutable state variable already initialized.
*/
