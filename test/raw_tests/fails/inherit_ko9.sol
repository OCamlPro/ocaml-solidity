interface I {
    function f() external view;
}

abstract contract CI is I {
}


abstract contract CJ is I {
    function f() external view override { }
}

contract C is CI, CJ {
    function f() external view override { }
}