interface I {
    function f() external;
}

contract C is I {
    function f() external override { }
}

contract D is I {
    function f() external override { }
}

contract E is C,D {
}