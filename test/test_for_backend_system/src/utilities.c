#include "utilities.h"
#include "project_globals.h"
#include "sensor_stub.h"

extern void __CPROVER_assert(_Bool condition, const char *description);

int process_input_and_update_counter(unsigned int input)
{
  // 4. LOOP UNWINDING:
  //    The loop is unrolled by CBMC up to the chosen unwind bound.
  for(unsigned int i = 0; i < input; i++)
  {
    global_counter++;
  }

  // 2. STUB FUNCTION USAGE:
  //    We read from the sensor stub multiple times
  //    (each call can yield a different nondet value).
  int sensor_val1 = read_sensor_stub();
  int sensor_val2 = read_sensor_stub();

  // Combine them in some way:
  int result = sensor_val1 + sensor_val2 + global_counter;

  // Optional extra check:
  __CPROVER_assert(result > -1000, "result is above -1000");

  return result;
}
