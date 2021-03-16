pragma solidity >=0.6.0;
// SPDX-License-Identifier: UNLICENSED

contract C1 {
  function f1() public pure {}
  function f2() public pure virtual {}
  function f3() public pure virtual {}
  function f4() public pure virtual {}
  function f5() public pure virtual {}
  function f6() public pure virtual {}
  function f7() public pure virtual {}
  function f8() public pure virtual {}
  function f9() public pure virtual {}
  function fa() public pure virtual {}
}

contract C1a is C1 {
  function f3() public pure override {}
  function f4() public pure override virtual {}
  function f5() public pure override virtual {}
  function f6() public pure override virtual {}
  function f7() public pure override(C1) {}
  function f8() public pure override(C1) virtual {}
  function f9() public pure override(C1) virtual {}
  function fa() public pure override(C1) virtual {}
}

contract C1b is C1a {
  function f5() public pure override {}
  function f6() public pure override virtual {}
  function f9() public pure override(C1a) {}
  function fa() public pure override(C1a) virtual {}
}

contract C2 {
  function f3() public pure virtual {}
  function f4() public pure virtual {}
  function f5() public pure virtual {}
  function f6() public pure virtual {}
  function f7() public pure virtual {}
  function f8() public pure virtual {}
  function f9() public pure virtual {}
  function fa() public pure virtual {}
}

contract C12a is C1, C2 {
  function f3() public pure override(C1,C2) {}
  function f4() public pure override(C1,C2) virtual {}
  function f5() public pure override(C1,C2) virtual {}
  function f6() public pure override(C1,C2) virtual {}
  function f7() public pure override(C1,C2) {}
  function f8() public pure override(C1,C2) virtual {}
  function f9() public pure override(C1,C2) virtual {}
  function fa() public pure override(C1,C2) virtual {}
}

contract C12b is C12a {
  function f5() public pure override {}
  function f6() public pure override virtual {}
  function f9() public pure override(C12a) {}
  function fa() public pure override(C12a) virtual {}
}
