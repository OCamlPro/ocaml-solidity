contract A {
    uint256 internal a;

    function fool(int256 b) external pure {
        b = b + 1;
    }

    // somfunc is `internal`
    function hof(function(int256) somfunc, int256 x) internal pure {
        x = x + 1;
    }

    function useHof() public {
        // `external` functions cannot be passed to functions expecting `internal` (even with `this`)
        hof(fool, 10);
        hof(this.fool, 10);
        a = 1 + 1;
    }
}
