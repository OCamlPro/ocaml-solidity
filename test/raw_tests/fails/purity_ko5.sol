pragma solidity >=0.6.0;
// SPDX-License-Identifier: UNLICENSED

contract C {
    address x;
    function f () public pure returns(uint){return x.balance;}
}

/* Error : Function declared as view, but this expression (potentially)
   modifies the state and thus require non-payable (the default) or
   payable. */