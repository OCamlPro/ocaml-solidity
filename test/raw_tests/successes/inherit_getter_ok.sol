pragma solidity >=0.6.0;
// SPDX-License-Identifier: UNLICENSED

contract C1 {
  function x() external virtual returns(int) {}
}

contract C2 {
  function x() external virtual returns(int) {}
}

contract C3 is C1 {
  int public override x;
}

contract C4 is C1 {
  int public override(C1) x;
}

contract C5 is C1, C2 {
  int public override(C1, C2) x;
}

