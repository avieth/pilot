#include <stdio.h>
#include "generated.c"

int main() {
  for (int i = 0; i < 15; ++i) {
    printf("%d ", eval());
  }
}
