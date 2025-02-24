#include "project_globals.h"
#include "utilities.h"

// Declare CBMC's nondeterministic unsigned int:
extern unsigned int nondet_uint();

// We can also declare the assume and assert built-ins here:
void __CPROVER_assume(_Bool condition);
void __CPROVER_assert(_Bool condition, const char *description);

int main()
{
  // 3. INPUT VARIABLE MODELING:
  //   Use a nondeterministic unsigned int for user_input:
  unsigned int user_input = nondet_uint();

  // Restrict the value of user_input (making it a realistic, bounded input):
  __CPROVER_assume(user_input <= 5);

  // For demonstration, also randomize the global with an assumption:
  global_counter = (int)nondet_uint();
  __CPROVER_assume(global_counter >= 0 && global_counter <= 10);

  // 4. LOOP UNWINDING (inside process_input_and_update_counter):
  int final_value = process_input_and_update_counter(user_input);

  // A simple assertion to check that final_value is nonnegative:
  __CPROVER_assert(final_value >= 0, "final_value is nonnegative");

  return 0;
}
