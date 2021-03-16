// SPDX-License-Identifier: UNLICENSED
pragma solidity >=0.7.0;

contract C {
    function x() external view virtual returns (int) {}
}

contract C_pub is C {
    int public override x;
}

contract C_priv is C {
    int private x;
}

contract C_int is C {
    int internal x;
}

