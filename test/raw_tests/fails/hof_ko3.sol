contract A {
    uint256 internal a;

    function fool(int256 b) private pure {
        b = b + 1;
    }

    function hof(function(int256) external somfunc, int256 x) internal pure {
        x = x + 1;
    }

    function useHof() public {
        // `private` functions cannot be passed to functions expecting `external`
        hof(fool, 10);
        a = 1 + 1;
    }
}
