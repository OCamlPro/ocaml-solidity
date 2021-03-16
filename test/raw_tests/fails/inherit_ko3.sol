pragma solidity >=0.6.0;
// SPDX-License-Identifier: UNLICENSED

contract C1 {
  function f() public pure {}
}

contract C2 {
  function f() public pure {}
}

contract C3 is C1, C2 {
}

/*
Error: Derived contract must override function "f". Two or more base classes define function with same name and parameter types.
*/
