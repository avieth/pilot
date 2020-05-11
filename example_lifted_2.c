#include <stdint.h>
#include <stdio.h>

/*
 * What follows was generated from this Haskell EDSL expression
 *
 *   pair (maybe (just (int8 42)) (int8 2) id) (uint8 255)
 *
 * The use of the pair has yielded the definition of product_0.
 *
 * Notice that, although products and sums are typically referenced by way of
 * pointers, the product returned from eval is not a pointer, which is good
 * because it's stack allocated.
 */

enum sum_tag_0 {tag_1 , tag_0};
struct product_0;
struct sum_0;
union sum_variant_0;
struct product_0
{ const uint8_t field_1;
  const int8_t field_0;
};
union sum_variant_0
{ const int8_t variant_1;
  const void *const restrict variant_0;
};
struct sum_0
{ const enum sum_tag_0 tag;
  const union sum_variant_0 variant;
};

struct product_0 eval() {
  const struct sum_0 *const restrict scrutinee_0_0 = &(struct sum_0){.tag = tag_1, .variant = {.variant_1 = 0x2A}};
  int8_t result_0_1;
  switch ((scrutinee_0_0)->tag) {
    {case tag_1: {result_0_1 = (scrutinee_0_0)->variant.variant_1;
                  break;};
     case tag_0: {result_0_1 = 0x2;
                  break;};}
  };
  return *(&(struct product_0){.field_1 = 0xFF, .field_0 = result_0_1});
}

/* End of generated C */

int main(void){
  struct product_0 x = eval();
  printf("(%d, %d)\n", x.field_0, x.field_1);
  return 0;
}
