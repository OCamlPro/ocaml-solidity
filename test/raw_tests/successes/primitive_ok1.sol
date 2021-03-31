
contract C {
function test() public {
    uint i;
    for (i = 0; i < 100; ++i) {
      assert((i * i) / i == i);
    }
  }}
