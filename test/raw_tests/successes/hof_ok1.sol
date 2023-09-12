contract A {
    uint256 internal a;

    function fool(int256 b) public pure {
        b = b + 1;
    }

    // somfunc is `internal`
    function hof(function(int256) somfunc, int256 x) internal pure {
        x = x + 1;
    }

    function useHof() public {
        // `public` functions can be passed to functions expecting `internal`
        hof(fool, 10);
        a = 1 + 1;
    }
}
