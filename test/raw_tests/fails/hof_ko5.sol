contract A {
    uint256 internal a;

    function fool(int256 b) internal pure {
        b = b + 1;
    }

    // `public` functions cannot have `internal` function-type arguments
    function hof(function(int256) internal somfunc, int256 x) public pure {
        x = x + 1;
    }
}
