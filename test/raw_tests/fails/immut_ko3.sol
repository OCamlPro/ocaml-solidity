pragma solidity >=0.6.0;
// SPDX-License-Identifier: UNLICENSED

contract C {
  int y = x;
  int immutable x = 42;
}

/*
Error: Immutable variables cannot be read during contract creation time, which means they cannot be read in the constructor or any function or modifier called from it.
*/
