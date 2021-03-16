// SPDX-License-Identifier: UNLICENSED
pragma solidity >=0.7.0;

contract C {
    function x() external view returns (int) {}
}

contract C_priv is C {
    int private x;
}

contract C_int is C {
    int internal x;
}

