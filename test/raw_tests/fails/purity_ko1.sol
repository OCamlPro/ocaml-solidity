pragma solidity >=0.6.0;
// SPDX-License-Identifier: UNLICENSED

contract C {
  function g () pure {f ();}
  function f () view {}
}

/* Error : Function declared as pure, but this  expression (potentially)
   reads from the environment or state and thus require "view". */