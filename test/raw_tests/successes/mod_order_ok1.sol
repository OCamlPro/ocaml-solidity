// SPDX-License-Identifier: UNLICENSED
pragma solidity >=0.7.0;

/*
./ix client originate contract mod transferring 0 from bootstrap1 running solidity_examples/mod_order_ok1.sol --init '#solidity:C()' --burn-cap 2

./ix client transfer 0 from bootstrap1 to mod --entrypoint "f" --arg '#sol:()' --burn-cap 1

*/

contract C {
    int i = 0;
    modifier M1(int ii) {
        assert(ii == 1); assert(i == 1);
        i+=4; _;
        assert(ii == 1); assert(i == 183);
        i+=8; _;
        assert(ii == 1); assert(i == 369);
    }
    modifier M2(int ii) {
        assert(ii == 7 || ii == 193); assert(i == 7 || i == 193);
        i+=16; _;
        assert(ii == 7 || ii == 193); assert(i == 87 || i == 273);
        i+=32; _;
        assert(ii == 7 || ii == 193); assert(i == 183 || i == 369);
    }
    function f() public M1(i+=1) M2(i+=2) {
        assert(i == 23 || i == 119 || i == 209 || i == 305); i+=64;
    }
}

