// TODO don't hard-code here
#define RV_wXLEN_IM RV32IM

void run(size_t n, RiscvState s) {
  for (size_t i = 0; i < n; i++) {
    t pc = getPC(s);
    int32_t inst = loadWord(s, pc);
    execute(s, decode(RV_wXLEN_IM, inst));
    step(s);
  }
}
