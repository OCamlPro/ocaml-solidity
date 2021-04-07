pragma solidity >=0.6.0;
// SPDX-License-Identifier: UNLICENSED

contract C {
  int y = 12;
  int constant x = y;
}

/*
Error: Initial value for constant variable has to be compile-time constant.
*/
