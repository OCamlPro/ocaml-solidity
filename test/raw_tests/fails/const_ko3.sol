pragma solidity >=0.6.0;
// SPDX-License-Identifier: UNLICENSED

contract C {
  int constant x1 = x2;
  int constant x2 = x3;
  int constant x3 = x4;
  int constant x4 = x1;
}

/*
Error: The value of the constant x1 has a cyclic dependency via x2.
Error: The value of the constant x2 has a cyclic dependency via x3.
Error: The value of the constant x3 has a cyclic dependency via x4.
Error: The value of the constant x4 has a cyclic dependency via x1.
*/
