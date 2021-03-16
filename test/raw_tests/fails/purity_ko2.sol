pragma solidity >=0.6.0;
// SPDX-License-Identifier: UNLICENSED

contract C {
    int x;
    function f () public pure returns (int) { return x;}
}

/* Error : Function declared as pure, but this  expression (potentially)
   reads from the environment or state and thus require "view". */