pragma solidity >=0.6.0;
// SPDX-License-Identifier: UNLICENSED

contract C1 {
  int immutable x = 42;
}

contract C2 is C1 {
  function f() public { x = 42; }
}

/*
Error: Immutable variables can only be initialized inline or assigned directly in the constructor.
*/
