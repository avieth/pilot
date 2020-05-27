#include <stdio.h>
#include "generated.c"

// The generated C has 3 inputs, which we define here, and one output, which
// we declare extern.

struct sum_0 input_c = { .tag = tag_0, .variant = { .variant_0 = NULL } };
struct sum_0 input_b = { .tag = tag_0, .variant = { .variant_0 = NULL } };
struct sum_0 input_a = { .tag = tag_0, .variant = { .variant_0 = NULL } };
extern struct sum_0 output_x;

// Will call this after each eval() from the generated C. The eval() updates
// output_x.
//
// We "just know" the encoding of Maybe and yes that's not ideal. Must think of
// a nice way to do marshalling from the EDSL types to particular C types of
// the shell program.
void print_result() {
  switch (output_x.tag) {
    case tag_1:
      printf("Just %d\n", output_x.variant.variant_1);
      break;
    case tag_0:
      printf("Nothing\n");
      break;
  }
}

int main(void) {

  // Only a is Just. Will show Nothing.
  input_a = (struct sum_0){ .tag = tag_1, .variant = { .variant_1 = 19 } };
  eval();
  print_result();

  // Only a and b are Just. Will show Nothing.
  input_b = (struct sum_0){ .tag = tag_1, .variant = { .variant_1 = 23 } };
  eval();
  print_result();

  // All are Just. Will show Just 42.
  input_c = (struct sum_0){ .tag = tag_1, .variant = { .variant_1 = 0 } };
  eval();
  print_result();

  return 0;
}
