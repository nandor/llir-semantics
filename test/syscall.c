
static __inline long __syscall0(long n)
{
  unsigned long ret;
  __asm__ __volatile__ ("syscall" : "=a"(ret) : "a"(n) : "rcx", "r11", "memory");
  return ret;
}

int main() {
  return __syscall0(1000);
}
