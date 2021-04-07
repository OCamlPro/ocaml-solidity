pragma solidity >=0.6.0;
// SPDX-License-Identifier: UNLICENSED

contract C {
  constructor() public {}
  int immutable x;
}

/*
Error: Construction control flow ends without initializing all immutable state variables.
*/
