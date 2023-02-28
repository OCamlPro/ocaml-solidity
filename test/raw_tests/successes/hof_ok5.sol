contract A {
    uint256 internal a;

    function fool(int256 b) external pure {
        b = b + 1;
    }

    function hof(function(int256) external somfunc, int256 x) internal pure {
        x = x + 1;
    }

    function useHof() public {
        // `external` functions can be passed to functions expecting `external`, using `this`
        hof(this.fool, 10);
        a = 1 + 1;
    }
}
