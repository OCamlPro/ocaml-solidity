pragma solidity >=0.6.0;
// SPDX-License-Identifier: UNLICENSED

contract C1 {
  function f() public pure virtual {}
}

contract C2 is C1 {
  function f() public pure override {}
}

contract C3 is C2 {
  function f() public pure override {}
}

/*
Error: Trying to override non-virtual function. Did you forget to add "virtual"?
*/
