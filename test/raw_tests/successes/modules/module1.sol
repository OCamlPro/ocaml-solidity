pragma solidity >=0.6.0;

import "./module2.sol";

contract D is C {

}

import "./module2.sol" as M2;

contract E is M2.C {

}

contract F is M2.M1.M2.M1.M2.C {

}

import { C as G } from "./module2.sol";

contract H is G {

}

//import { f as g, x as y } from "./module2.sol";
//int constant y = 42;
contract I {

    function f(int z) public returns(int) {
       return g(z + y);
    }


    function h() public pure returns(int) {
      return y;
    }
}
