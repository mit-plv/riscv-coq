// Note: Filtering of unsupported instructions was already done in Decode.
// Note: We don't support CSR instructions yet.
void execute(RiscvState s, Instruction inst) {
  switch (inst.kind) {
  case K_IInstruction:
    executeI(s, inst.as_IInstruction.f0);
    break;
  case K_MInstruction:
    executeM(s, inst.as_MInstruction.f0);
    break;
  case K_I64Instruction:
    executeI64(s, inst.as_I64Instruction.f0);
    break;
  case K_M64Instruction:
    executeM64(s, inst.as_M64Instruction.f0);
    break;
  default:
    raiseException(s, 0, 2);
  }
}
