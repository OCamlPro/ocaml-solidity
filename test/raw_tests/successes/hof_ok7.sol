contract A {
    uint256 internal a;

    function fool(int256 b) internal pure {
        b = b + 1;
    }

    // somfunc is `internal`
    function hof(function(int256) somfunc, int256 x) internal pure {
        x = x + 1;
    }

    function hofhof(function(function(int256), int256) somotherfunc, int256 x) internal {
        x = x + 1;
    }

    function useHof() public {
        hof(fool, 10);
        hofhof(hof, 10);
        a = 1 + 1;
    }
}
