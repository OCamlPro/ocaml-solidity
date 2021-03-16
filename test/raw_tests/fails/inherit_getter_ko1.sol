pragma solidity >=0.6.0;
// SPDX-License-Identifier: UNLICENSED

contract C1 {
  function x() external virtual returns(int) {}
}

contract C2 is C1 {
  int public x;
}

/*
Error: Overriding public state variable is missing "override" specifier.
*/
