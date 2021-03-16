// SPDX-License-Identifier: UNLICENSED
pragma solidity >=0.7.0;

/*
./ix client originate contract ctor transferring 0 from bootstrap1 running solidity_examples/ctor_order_ok1.sol --init '#solidity:C()' --burn-cap 2

*/

contract C0 {
    int i = 0;
}

contract CA1 is C0 {
    constructor(int ii) { assert(ii == 63); assert(i == 63); i+=64; }
}

contract CA2 is C0 {
    constructor(int ii) { assert(ii == 47); assert(i == 127); i+=128; }
}

contract CA is CA1, CA2 {
    constructor(int ii) CA1(i+=16) CA2(i+=32) { assert(ii == 15); assert(i == 255); i+=256; }
}

contract CB1 is C0 {
    constructor(int ii) { assert(ii == 14); assert(i == 511); i+=512; }
}

contract CB2 is C0 {
    constructor(int ii) { assert(ii == 10); assert(i == 1023); i+=1024; }
}

contract CB is CB1, CB2 {
    constructor(int ii) CB1(i+=4) CB2(i+=8) { assert(ii == 2); assert(i == 2047); i+=2048; }
}

contract C is CA, CB {
    constructor() CA(i+=1) CB(i+=2) { assert(i == 4095); }
}

