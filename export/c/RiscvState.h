typedef struct {
  t *registers;
  int32_t *memory;
  t* pc;
  t* nextPC;
  t* exceptionHandlerAddr;
} RiscvState;


t getRegister(RiscvState s, Register reg) {
  if (reg == 0) {
    return 0;
  } else {
    return s.memory[reg];
  }
}

void setRegister(RiscvState s, Register reg, t v) {
  if (reg != 0) {
    s.registers[reg] = v;
  }
}

t getPC(RiscvState s) {
  return *s.pc;
}

void setPC(RiscvState s, t newPC) {
  *s.nextPC = newPC;
}

uint8_t loadByte(RiscvState s, t addr) {
  return 0; // TODO
}

uint16_t loadHalf(RiscvState s, t addr) {
  return 0; // TODO
}

uint32_t loadWord(RiscvState s, t addr) {
  return s.memory[addr/4];
}

uint64_t loadDouble(RiscvState s, t addr) {
  return 0; // TODO
}

void storeByte(RiscvState s, t addr, uint8_t v) {
  // TODO
}

void storeHalf(RiscvState s, t addr, uint16_t v) {
  // TODO
}

void storeWord(RiscvState s, t addr, uint32_t v) {
  // TODO
}

void storeDouble(RiscvState s, t addr, uint64_t v) {
  // TODO
}

void step(RiscvState s) {
  *s.pc = *s.nextPC;
  *s.nextPC = *s.nextPC + 4;
}

t getCSRField_MTVecBase(RiscvState s) {
  return *s.exceptionHandlerAddr;
}

void endCycle(RiscvState s) {
  // TODO
}

void raiseException(RiscvState s, t isInterrupt, t exceptionCode) {
  t addr = getCSRField_MTVecBase(s);
  setPC(s, addr * 4);
  endCycle(s);
}

typedef enum {AccessTypeLoad, AccessTypeStore} AccessType;

t translate(RiscvState s, AccessType accessType, t alignment, t addr) {
  // in a system with virtual memory, this would also do the translation, but in our
  // case, we only verify the alignment
  if (addr % alignment == 0) {
    return addr;
  } else {
    raiseException(s, 0, 4);
  }
}
