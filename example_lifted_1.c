#include <stdint.h>
#include <stdio.h>

int8_t eval(void);

int main(void){
  printf("%d\n", eval());
  return 0;
}

/*
 * What follows was generated from this Haskell EDSL expression
 *
 *   maybe (just (int8 42)) (int8 2) id
 *
 * The use of the Maybe type, its representation as a sum 1 + t, and its
 * specialization at int8, causes the C generator to define an enum, struct, and
 * union to represent the monomorphic type 1 + int8
 *
 * The expression uses a sum eliminator, which is elaborated to a switch
 * statement, so that each branch may have its own scope.
 *
 * All sums and products are represented by pointers, so that the C compiler
 * always knows their sizes (essential for declaring nested sums and products).
 * These pointers are const restrict because the EDSL is pure functional: the
 * C backend does not generate any destructive updates. Although it may alias
 * pointers, all pointers are read-only, so restrict is OK.
 */

enum sum_tag_0 {tag_1 , tag_0};
struct sum_0;
union sum_variant_0;
union sum_variant_0
{ const int8_t variant_1;
  const void *const restrict variant_0;
};
struct sum_0
{ const enum sum_tag_0 tag;
  const union sum_variant_0 variant;
};

int8_t eval() {
  const struct sum_0 *const restrict scrutinee_0_0 = &(struct sum_0){.tag = tag_1, .variant = {.variant_1 = 0x2A}};
  int8_t result_0_1;
  switch ((scrutinee_0_0)->tag) {
    {case tag_1: {result_0_1 = (scrutinee_0_0)->variant.variant_1;
                  break;};
     case tag_0: {result_0_1 = 0x2;
                  break;};}
  };
  return result_0_1;
}
