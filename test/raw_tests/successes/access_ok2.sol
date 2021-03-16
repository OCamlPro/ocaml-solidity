contract D {
  enum e { a, b }
  struct s { int x; }
}

contract C is D {
  e v1 = e.a;
  s v2 = s({ x: 42 });
}