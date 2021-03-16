pragma solidity >=0.6.0;
// SPDX-License-Identifier: UNLICENSED

contract C {
  function f() public returns(int) { return 42; }
  int constant x = f();
}

/*
Error: Initial value for constant variable has to be compile-time constant.
*/
