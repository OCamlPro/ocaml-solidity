pragma solidity >=0.6.0;
// SPDX-License-Identifier: UNLICENSED

contract C {
  function j () {i ();}
  function i () payable {h ();}
  function h () view {g ();}
  function g () pure {f ();}
  function f () pure {f2 ();}
  function f2 () pure {f ();}
  
}