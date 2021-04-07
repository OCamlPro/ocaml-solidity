pragma solidity >=0.6.0;
// SPDX-License-Identifier: UNLICENSED

contract C {
    mapping(int => int) x;
    function f () public view { x[3] = 4;}
}

/* Error : Function declared as view, but this expression (potentially)
   modifies the state and thus require non-payable (the default) or
   payable. */