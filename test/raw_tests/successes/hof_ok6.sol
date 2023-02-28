contract A {
    uint256 internal a;

    function fool(int256 b) internal pure {
        b = b + 1;
    }

    // `public` functions can have `external` function-type arguments
    function hof(function(int256) external somfunc, int256 x) public pure {
        x = x + 1;
    }

    // `private` functions can have `external` function-type arguments
    function hof2(function(int256) external somfunc, int256 x) private pure {
        x = x + 1;
    }

    // `private` functions can have `internal` function-type arguments
    function hof3(function(int256) internal somfunc, int256 x) private pure {
        x = x + 1;
    }

    // `internal` functions can have `internal` function-type arguments
    function hof4(function(int256) internal somfunc, int256 x) internal pure {
        x = x + 1;
    }

    // `internal` functions can have `external` function-type arguments
    function hof5(function(int256) external somfunc, int256 x) internal pure {
        x = x + 1;
    }

    // `external` functions can have `external` function-type arguments
    function hof6(function(int256) external somfunc, int256 x) external pure {
        x = x + 1;
    }

    // The other two combinations that fail (interal-external) and (internal-public)
    //   are in `fails/hof_ko4.sol` and `fails/hof_ko5.sol` respectively
}
