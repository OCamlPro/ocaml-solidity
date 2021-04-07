pragma solidity >=0.6.0;
// SPDX-License-Identifier: UNLICENSED

contract C1 {
  function x() external virtual returns(int) {}
}

contract C2 {
  int public override(C1, C2) x;
}

contract C3 is C1, C2 {

}

/*
Error: Derived contract must override function "x". Two or more base classes define function with same name and parameter types. Since one of the bases defines a public state variable which cannot be overridden, you have to change the inheritance layout or the names of the functions.
*/
