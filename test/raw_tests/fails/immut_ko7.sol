pragma solidity >=0.6.0;
// SPDX-License-Identifier: UNLICENSED

contract C {
  function f() public { x = 42; }
  constructor() public { f(); }
  int immutable x;
}

/*
Error: Immutable variables can only be initialized inline or assigned directly in the constructor.
*/
