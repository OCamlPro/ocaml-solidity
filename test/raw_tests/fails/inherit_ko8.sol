pragma solidity >=0.6.0;
// SPDX-License-Identifier: UNLICENSED

contract C1 {
  function f() public pure virtual {}
}

contract C2 {
  function f() public pure virtual {}
}

contract C3 is C1, C2 {
  function f() public pure override {}
}

/*
Error: Function needs to specify overridden contracts "C1" and "C2".
*/
