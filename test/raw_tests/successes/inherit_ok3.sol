pragma solidity >=0.6.0;
// SPDX-License-Identifier: UNLICENSED

contract C1 {
  function f3() public pure virtual {}
}

contract C1a is C1 {
  function f3() public pure override {}
}

contract C1b is C1a {
}