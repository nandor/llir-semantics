unsigned fib(unsigned n) {
  unsigned a = 0, b = 1;
  while (n--) {
    unsigned c = a + b;
    a = b;
    b = c;
  }
  return b;
}
