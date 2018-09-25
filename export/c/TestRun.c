#include <stdint.h>
#include <stdlib.h>
#include <stdio.h>

#define t int32_t
#define t_signed int32_t
#define t_unsigned uint32_t
#define MAX_t_SIGNED   0x7fffffff
#define MIN_t_SIGNED  -0x80000000
#define MAX_t_UNSIGNED 0xffffffff

#include "Utility.h"
#include "Decode.h"

#include "RiscvState.h"

#include "ExecuteI64.h"
#include "ExecuteI.h"
#include "ExecuteM64.h"
#include "ExecuteM.h"

#include "Execute.h"
#include "Run.h"

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
  t regs[32];
  RiscvState initial;
  initial.registers = regs;
  initial.memory = fib6_riscv;
  initial.pc = 0;
  initial.nextPC = 4;
  initial.exceptionHandlerAddr = 666;

  int N = 200;
  run(N, initial);

  printf("Register values after %d execution steps:\n", N);
  for (int i = 1; i < 32; i++) {
    printf("x%d = %d\n", i, regs[i]);
  }
}
