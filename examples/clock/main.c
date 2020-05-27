#include <stdio.h>
#include "generated.c"

int main() {
  for (int i = 0; i < 15; ++i) {
    // It just so happens that the tag for booleans corresponds to the
    // _opposite_ of the typical 1 is true 0 is false encoding (although we
    // don't define the enum to guarantee that).
    printf("%d ", !(eval().tag));
  }
}
