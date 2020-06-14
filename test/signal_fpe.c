#include <unistd.h>
#include <signal.h>
#include <stdlib.h>

void handler(int signum)
{
  exit(0x08);
}

int main(int argc, char **argv)
{
  struct sigaction act_old;
  struct sigaction act_new =
    { .sa_handler = handler
    , .sa_flags = SA_NODEFER
    };
  sigaction(SIGFPE, &act_new, &act_old);
  return 5 / read(STDIN_FILENO, NULL, 0);
}
