// SPDX-License-Identifier: UNLICENSED
pragma solidity >=0.7.0;

contract C1 {
    function x() private view returns (int) {}
    function y() private view returns (int) {}
}

contract C2 is C1 {
    int private x;
    int internal y;
}
