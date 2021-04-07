pragma solidity >=0.6.0;
// SPDX-License-Identifier: UNLICENSED

contract C1 {
  function f() public pure virtual {}
}

contract C2 is C1 {
  function f() public pure {}
}

/*
Error: Overriding function is missing "override" specifier.
*/
