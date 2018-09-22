#include <stdint.h>
#include <stdlib.h>
#include <stdio.h>

int32_t fib6_riscv[] = {
  0x00600993,
  0x00000a13,
  0x00100913,
  0x00000493,
  0x0140006f,
  0x012a0ab3,
  0x00090a13,
  0x000a8913,
  0x00148493,
  0xff34c8e3
};

int main() {
  size_t N = sizeof(fib6_riscv) / sizeof(fib6_riscv[0]);
  for (size_t i = 0; i < N; i++) {
    printf("Should decode %d\n", fib6_riscv[i]);
  }
}
