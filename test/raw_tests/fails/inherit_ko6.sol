pragma solidity >=0.6.0;
// SPDX-License-Identifier: UNLICENSED

contract C1 {
  function f() public pure override {}
}

/*
Error: Function has override specified but does not override anything.
*/
