contract W1 {
    modifier m1() virtual { _; }
}

contract W2 is W1 {
   modifier m1() virtual override { _; }
}

contract W3 is W1, W2 {
    modifier m1() override(W1, W2) { _; }    
}
