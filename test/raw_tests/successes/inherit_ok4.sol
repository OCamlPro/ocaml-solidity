interface I {
    function f() external view;
}

abstract contract CI is I {
}

contract C is CI {
    function f() external view override { }
}