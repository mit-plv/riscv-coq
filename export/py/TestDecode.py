from Decode import *

fib6_riscv = [
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
]

for z in fib6_riscv:
    inst = decode(InstructionSet.RV32IM, z)
    print(inst.f0)
