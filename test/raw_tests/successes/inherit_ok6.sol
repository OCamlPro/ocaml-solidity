interface I {
    function f() external;
}

contract C is I {
    function f() external override { }
}

contract D is C {
}

contract E is I, D {
}