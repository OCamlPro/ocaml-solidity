pragma solidity >=0.6.0;
// SPDX-License-Identifier: UNLICENSED

contract C1 {
  function x() external returns(int) {}
}

contract C2 is C1 {
  int public override x;
}

/*
Error: Trying to override non-virtual function. Did you forget to add "virtual"?
*/
