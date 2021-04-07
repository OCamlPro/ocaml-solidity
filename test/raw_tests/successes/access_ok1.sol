pragma solidity  >=0.6.0;
contract C {
  struct s {
    int[4] a;
  } s ia;

  int[4] ia2 = ia.a; // problème ici avec l'expression de droite, quand il s'agit d'un FieldExpression
  function f() public {
        int[4] storage iap = ia.a;
        iap[3] = 42;
    }
  function g() public view returns (int) {
        return ia.a[3];
  }
}
