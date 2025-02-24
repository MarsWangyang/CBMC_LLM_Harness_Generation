#include "sensor_stub.h"

// Declare CBMC's nondeterministic function signature.
// (You can also do this in a shared header, but here it's local for brevity.)
extern int nondet_int();

int read_sensor_stub(void)
{
  // Stub out sensor reading as a nondeterministic value:
  return nondet_int();
}
