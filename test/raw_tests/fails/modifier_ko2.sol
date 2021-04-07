contract W1 {
    modifier m1() { _; }
}

contract W3 is W1 {
    modifier m1() override { _; }
}

/*
Error: Trying to override non-virtual modifier. Did you forget to add "virtual"?
*/