(* Need to define Register *)
Require Import Coq.ZArith.ZArith.
Require Import riscv.Spec.Decode.
Require Import riscv.Utility.Utility.

Local Open Scope Z_scope.

Record InstructionMapper{T: Type} := mkInstructionMapper {
  map_Invalid: Z -> T;
  map_R(opcode: MachineInt)(rd rs1 rs2: Register)(funct3: MachineInt)(funct7: MachineInt): T;
  map_R_atomic(opcode: MachineInt)(rd rs1 rs2: Register)(funct3: MachineInt)(aqrl: MachineInt)(funct5: MachineInt): T;
  map_I(opcode: MachineInt)(rd rs1: Register)(funct3: MachineInt)(oimm12: Z): T;
  map_I_shift_57(opcode: MachineInt)(rd rs1: Register)(shamt5 funct3 funct7: MachineInt): T;
  map_I_shift_66(opcode: MachineInt)(rd rs1: Register)(shamt6 funct3 funct6: MachineInt): T;
  map_I_system(opcode: MachineInt)(rd rs1: Register)(funct3 funct12: MachineInt): T;
  map_S(opcode: MachineInt)(rs1 rs2: Register)(funct3: MachineInt)(simm12: Z): T;
  map_SB(opcode: MachineInt)(rs1 rs2: Register)(funct3: MachineInt)(sbimm12: Z): T;
  map_U(opcode: MachineInt)(rd: Register)(imm20: Z): T;
  map_UJ(opcode: MachineInt)(rd: Register)(jimm20: Z): T;
  map_Fence(opcode: MachineInt)(rd rs1: Register)(funct3: MachineInt)(prd scc msb4: MachineInt): T;
  map_FenceI(opcode: MachineInt)(rd rs1: Register)(funct3: MachineInt)(imm12: MachineInt): T;
}.

Arguments InstructionMapper: clear implicits.

Definition apply_InstructionMapper{T: Type}(mapper: InstructionMapper T)(inst: Instruction): T :=
  match inst with
  | InvalidInstruction inst   => mapper.(map_Invalid) inst
  | IInstruction   InvalidI   => mapper.(map_Invalid) 0
  | MInstruction   InvalidM   => mapper.(map_Invalid) 0
  | AInstruction   InvalidA   => mapper.(map_Invalid) 0
  | I64Instruction InvalidI64 => mapper.(map_Invalid) 0
  | M64Instruction InvalidM64 => mapper.(map_Invalid) 0
  | A64Instruction InvalidA64 => mapper.(map_Invalid) 0
  | CSRInstruction InvalidCSR => mapper.(map_Invalid) 0

  (* encoding floating point is not supported at the moment *)
  | FInstruction   _ => mapper.(map_Invalid) 0
  | F64Instruction _ => mapper.(map_Invalid) 0

  | IInstruction   (Lb  rd rs1 oimm12) => mapper.(map_I) opcode_LOAD rd rs1 funct3_LB  oimm12
  | IInstruction   (Lh  rd rs1 oimm12) => mapper.(map_I) opcode_LOAD rd rs1 funct3_LH  oimm12
  | IInstruction   (Lw  rd rs1 oimm12) => mapper.(map_I) opcode_LOAD rd rs1 funct3_LW  oimm12
  | I64Instruction (Ld  rd rs1 oimm12) => mapper.(map_I) opcode_LOAD rd rs1 funct3_LD  oimm12
  | IInstruction   (Lbu rd rs1 oimm12) => mapper.(map_I) opcode_LOAD rd rs1 funct3_LBU oimm12
  | IInstruction   (Lhu rd rs1 oimm12) => mapper.(map_I) opcode_LOAD rd rs1 funct3_LHU oimm12
  | I64Instruction (Lwu rd rs1 oimm12) => mapper.(map_I) opcode_LOAD rd rs1 funct3_LWU oimm12

  | IInstruction (Fence pred succ) => mapper.(map_Fence) opcode_MISC_MEM 0 0 funct3_FENCE pred succ 0
  | IInstruction (Fence_i) =>         mapper.(map_FenceI) opcode_MISC_MEM 0 0 funct3_FENCE_I 0

  | IInstruction (Addi  rd rs1 imm12 ) => mapper.(map_I) opcode_OP_IMM rd rs1 funct3_ADDI imm12
  | IInstruction (Slli  rd rs1 shamt6) => mapper.(map_I_shift_66) opcode_OP_IMM rd rs1 shamt6 funct3_SLLI funct6_SLLI
  | IInstruction (Slti  rd rs1 imm12 ) => mapper.(map_I) opcode_OP_IMM rd rs1 funct3_SLTI imm12
  | IInstruction (Sltiu rd rs1 imm12 ) => mapper.(map_I) opcode_OP_IMM rd rs1 funct3_SLTIU imm12
  | IInstruction (Xori  rd rs1 imm12 ) => mapper.(map_I) opcode_OP_IMM rd rs1 funct3_XORI imm12
  | IInstruction (Ori   rd rs1 imm12 ) => mapper.(map_I) opcode_OP_IMM rd rs1 funct3_ORI imm12
  | IInstruction (Andi  rd rs1 imm12 ) => mapper.(map_I) opcode_OP_IMM rd rs1 funct3_ANDI imm12
  | IInstruction (Srli  rd rs1 shamt6) => mapper.(map_I_shift_66) opcode_OP_IMM rd rs1 shamt6 funct3_SRLI funct6_SRLI
  | IInstruction (Srai  rd rs1 shamt6) => mapper.(map_I_shift_66) opcode_OP_IMM rd rs1 shamt6 funct3_SRAI funct6_SRAI

  | IInstruction (Auipc rd oimm20) => mapper.(map_U) opcode_AUIPC rd oimm20

  | I64Instruction (Addiw rd rs1 imm12) => mapper.(map_I) opcode_OP_IMM_32 rd rs1 funct3_ADDIW imm12
  | I64Instruction (Slliw rd rs1 shm5 ) => mapper.(map_I_shift_57) opcode_OP_IMM_32 rd rs1 shm5 funct3_SLLI funct7_SLLIW
  | I64Instruction (Srliw rd rs1 shm5 ) => mapper.(map_I_shift_57) opcode_OP_IMM_32 rd rs1 shm5 funct3_SRLI funct7_SRLIW
  | I64Instruction (Sraiw rd rs1 shm5 ) => mapper.(map_I_shift_57) opcode_OP_IMM_32 rd rs1 shm5 funct3_SRAI funct7_SRAIW

  | IInstruction   (Sb rs1 rs2 simm12) => mapper.(map_S) opcode_STORE rs1 rs2 funct3_SB simm12
  | IInstruction   (Sh rs1 rs2 simm12) => mapper.(map_S) opcode_STORE rs1 rs2 funct3_SH simm12
  | IInstruction   (Sw rs1 rs2 simm12) => mapper.(map_S) opcode_STORE rs1 rs2 funct3_SW simm12
  | I64Instruction (Sd rs1 rs2 simm12) => mapper.(map_S) opcode_STORE rs1 rs2 funct3_SD simm12

  | IInstruction (Add    rd rs1 rs2) => mapper.(map_R) opcode_OP rd rs1 rs2 funct3_ADD    funct7_ADD
  | IInstruction (Sub    rd rs1 rs2) => mapper.(map_R) opcode_OP rd rs1 rs2 funct3_SUB    funct7_SUB
  | IInstruction (Sll    rd rs1 rs2) => mapper.(map_R) opcode_OP rd rs1 rs2 funct3_SLL    funct7_SLL
  | IInstruction (Slt    rd rs1 rs2) => mapper.(map_R) opcode_OP rd rs1 rs2 funct3_SLT    funct7_SLT
  | IInstruction (Sltu   rd rs1 rs2) => mapper.(map_R) opcode_OP rd rs1 rs2 funct3_SLTU   funct7_SLTU
  | IInstruction (Xor    rd rs1 rs2) => mapper.(map_R) opcode_OP rd rs1 rs2 funct3_XOR    funct7_XOR
  | IInstruction (Srl    rd rs1 rs2) => mapper.(map_R) opcode_OP rd rs1 rs2 funct3_SRL    funct7_SRL
  | IInstruction (Sra    rd rs1 rs2) => mapper.(map_R) opcode_OP rd rs1 rs2 funct3_SRA    funct7_SRA
  | IInstruction (Or     rd rs1 rs2) => mapper.(map_R) opcode_OP rd rs1 rs2 funct3_OR     funct7_OR
  | IInstruction (And    rd rs1 rs2) => mapper.(map_R) opcode_OP rd rs1 rs2 funct3_AND    funct7_AND
  | MInstruction (Mul    rd rs1 rs2) => mapper.(map_R) opcode_OP rd rs1 rs2 funct3_MUL    funct7_MUL
  | MInstruction (Mulh   rd rs1 rs2) => mapper.(map_R) opcode_OP rd rs1 rs2 funct3_MULH   funct7_MULH
  | MInstruction (Mulhsu rd rs1 rs2) => mapper.(map_R) opcode_OP rd rs1 rs2 funct3_MULHSU funct7_MULHSU
  | MInstruction (Mulhu  rd rs1 rs2) => mapper.(map_R) opcode_OP rd rs1 rs2 funct3_MULHU  funct7_MULHU
  | MInstruction (Div    rd rs1 rs2) => mapper.(map_R) opcode_OP rd rs1 rs2 funct3_DIV    funct7_DIV
  | MInstruction (Divu   rd rs1 rs2) => mapper.(map_R) opcode_OP rd rs1 rs2 funct3_DIVU   funct7_DIVU
  | MInstruction (Rem    rd rs1 rs2) => mapper.(map_R) opcode_OP rd rs1 rs2 funct3_REM    funct7_REM
  | MInstruction (Remu   rd rs1 rs2) => mapper.(map_R) opcode_OP rd rs1 rs2 funct3_REMU   funct7_REMU

  | IInstruction (Lui rd imm20) => mapper.(map_U) opcode_LUI rd imm20

  | I64Instruction (Addw  rd rs1 rs2) => mapper.(map_R) opcode_OP_32 rd rs1 rs2 funct3_ADDW  funct7_ADDW
  | I64Instruction (Subw  rd rs1 rs2) => mapper.(map_R) opcode_OP_32 rd rs1 rs2 funct3_SUBW  funct7_SUBW
  | I64Instruction (Sllw  rd rs1 rs2) => mapper.(map_R) opcode_OP_32 rd rs1 rs2 funct3_SLLW  funct7_SLLW
  | I64Instruction (Srlw  rd rs1 rs2) => mapper.(map_R) opcode_OP_32 rd rs1 rs2 funct3_SRLW  funct7_SRLW
  | I64Instruction (Sraw  rd rs1 rs2) => mapper.(map_R) opcode_OP_32 rd rs1 rs2 funct3_SRAW  funct7_SRAW
  | M64Instruction (Mulw  rd rs1 rs2) => mapper.(map_R) opcode_OP_32 rd rs1 rs2 funct3_MULW  funct7_MULW
  | M64Instruction (Divw  rd rs1 rs2) => mapper.(map_R) opcode_OP_32 rd rs1 rs2 funct3_DIVW  funct7_DIVW
  | M64Instruction (Divuw rd rs1 rs2) => mapper.(map_R) opcode_OP_32 rd rs1 rs2 funct3_DIVUW funct7_DIVUW
  | M64Instruction (Remw  rd rs1 rs2) => mapper.(map_R) opcode_OP_32 rd rs1 rs2 funct3_REMW  funct7_REMW
  | M64Instruction (Remuw rd rs1 rs2) => mapper.(map_R) opcode_OP_32 rd rs1 rs2 funct3_REMUW funct7_REMUW

  | IInstruction (Beq  rs1 rs2 sbimm12) => mapper.(map_SB) opcode_BRANCH rs1 rs2 funct3_BEQ  sbimm12
  | IInstruction (Bne  rs1 rs2 sbimm12) => mapper.(map_SB) opcode_BRANCH rs1 rs2 funct3_BNE  sbimm12
  | IInstruction (Blt  rs1 rs2 sbimm12) => mapper.(map_SB) opcode_BRANCH rs1 rs2 funct3_BLT  sbimm12
  | IInstruction (Bge  rs1 rs2 sbimm12) => mapper.(map_SB) opcode_BRANCH rs1 rs2 funct3_BGE  sbimm12
  | IInstruction (Bltu rs1 rs2 sbimm12) => mapper.(map_SB) opcode_BRANCH rs1 rs2 funct3_BLTU sbimm12
  | IInstruction (Bgeu rs1 rs2 sbimm12) => mapper.(map_SB) opcode_BRANCH rs1 rs2 funct3_BGEU sbimm12

  | IInstruction (Jalr rd rs1 oimm12) => mapper.(map_I) opcode_JALR rd rs1 funct3_JALR oimm12
  | IInstruction (Jal rd jimm20) => mapper.(map_UJ) opcode_JAL rd jimm20

  | CSRInstruction (Ecall ) => mapper.(map_I_system) opcode_SYSTEM 0 0 funct3_PRIV funct12_ECALL
  | CSRInstruction (Ebreak) => mapper.(map_I_system) opcode_SYSTEM 0 0 funct3_PRIV funct12_EBREAK
  | CSRInstruction (Uret  ) => mapper.(map_I_system) opcode_SYSTEM 0 0 funct3_PRIV funct12_URET
  | CSRInstruction (Sret  ) => mapper.(map_I_system) opcode_SYSTEM 0 0 funct3_PRIV funct12_SRET
  | CSRInstruction (Mret  ) => mapper.(map_I_system) opcode_SYSTEM 0 0 funct3_PRIV funct12_MRET
  | CSRInstruction (Wfi   ) => mapper.(map_I_system) opcode_SYSTEM 0 0 funct3_PRIV funct12_WFI

  | CSRInstruction (Sfence_vma rs1 rs2) => mapper.(map_R) opcode_SYSTEM 0 rs1 rs2 funct3_PRIV funct7_SFENCE_VMA

  | CSRInstruction (Csrrw  rd rs1  csr12) => mapper.(map_I_system) opcode_SYSTEM rd rs1  funct3_CSRRW  csr12
  | CSRInstruction (Csrrs  rd rs1  csr12) => mapper.(map_I_system) opcode_SYSTEM rd rs1  funct3_CSRRS  csr12
  | CSRInstruction (Csrrc  rd rs1  csr12) => mapper.(map_I_system) opcode_SYSTEM rd rs1  funct3_CSRRC  csr12
  | CSRInstruction (Csrrwi rd zimm csr12) => mapper.(map_I_system) opcode_SYSTEM rd zimm funct3_CSRRWI csr12
  | CSRInstruction (Csrrsi rd zimm csr12) => mapper.(map_I_system) opcode_SYSTEM rd zimm funct3_CSRRSI csr12
  | CSRInstruction (Csrrci rd zimm csr12) => mapper.(map_I_system) opcode_SYSTEM rd zimm funct3_CSRRCI csr12

  | AInstruction   (Lr_w      rd rs1     aqrl) => mapper.(map_R_atomic) opcode_AMO rd rs1 0   funct3_AMOW aqrl funct5_LR
  | AInstruction   (Sc_w      rd rs1 rs2 aqrl) => mapper.(map_R_atomic) opcode_AMO rd rs1 rs2 funct3_AMOW aqrl funct5_SC
  | AInstruction   (Amoswap_w rd rs1 rs2 aqrl) => mapper.(map_R_atomic) opcode_AMO rd rs1 rs2 funct3_AMOW aqrl funct5_AMOSWAP
  | AInstruction   (Amoadd_w  rd rs1 rs2 aqrl) => mapper.(map_R_atomic) opcode_AMO rd rs1 rs2 funct3_AMOW aqrl funct5_AMOADD
  | AInstruction   (Amoxor_w  rd rs1 rs2 aqrl) => mapper.(map_R_atomic) opcode_AMO rd rs1 rs2 funct3_AMOW aqrl funct5_AMOXOR
  | AInstruction   (Amoand_w  rd rs1 rs2 aqrl) => mapper.(map_R_atomic) opcode_AMO rd rs1 rs2 funct3_AMOW aqrl funct5_AMOAND
  | AInstruction   (Amoor_w   rd rs1 rs2 aqrl) => mapper.(map_R_atomic) opcode_AMO rd rs1 rs2 funct3_AMOW aqrl funct5_AMOOR
  | AInstruction   (Amomin_w  rd rs1 rs2 aqrl) => mapper.(map_R_atomic) opcode_AMO rd rs1 rs2 funct3_AMOW aqrl funct5_AMOMIN
  | AInstruction   (Amomax_w  rd rs1 rs2 aqrl) => mapper.(map_R_atomic) opcode_AMO rd rs1 rs2 funct3_AMOW aqrl funct5_AMOMAX
  | AInstruction   (Amominu_w rd rs1 rs2 aqrl) => mapper.(map_R_atomic) opcode_AMO rd rs1 rs2 funct3_AMOW aqrl funct5_AMOMINU
  | AInstruction   (Amomaxu_w rd rs1 rs2 aqrl) => mapper.(map_R_atomic) opcode_AMO rd rs1 rs2 funct3_AMOW aqrl funct5_AMOMAXU
  | A64Instruction (Lr_d      rd rs1     aqrl) => mapper.(map_R_atomic) opcode_AMO rd rs1 0   funct3_AMOD aqrl funct5_LR
  | A64Instruction (Sc_d      rd rs1 rs2 aqrl) => mapper.(map_R_atomic) opcode_AMO rd rs1 rs2 funct3_AMOD aqrl funct5_SC
  | A64Instruction (Amoswap_d rd rs1 rs2 aqrl) => mapper.(map_R_atomic) opcode_AMO rd rs1 rs2 funct3_AMOD aqrl funct5_AMOSWAP
  | A64Instruction (Amoadd_d  rd rs1 rs2 aqrl) => mapper.(map_R_atomic) opcode_AMO rd rs1 rs2 funct3_AMOD aqrl funct5_AMOADD
  | A64Instruction (Amoxor_d  rd rs1 rs2 aqrl) => mapper.(map_R_atomic) opcode_AMO rd rs1 rs2 funct3_AMOD aqrl funct5_AMOXOR
  | A64Instruction (Amoand_d  rd rs1 rs2 aqrl) => mapper.(map_R_atomic) opcode_AMO rd rs1 rs2 funct3_AMOD aqrl funct5_AMOAND
  | A64Instruction (Amoor_d   rd rs1 rs2 aqrl) => mapper.(map_R_atomic) opcode_AMO rd rs1 rs2 funct3_AMOD aqrl funct5_AMOOR
  | A64Instruction (Amomin_d  rd rs1 rs2 aqrl) => mapper.(map_R_atomic) opcode_AMO rd rs1 rs2 funct3_AMOD aqrl funct5_AMOMIN
  | A64Instruction (Amomax_d  rd rs1 rs2 aqrl) => mapper.(map_R_atomic) opcode_AMO rd rs1 rs2 funct3_AMOD aqrl funct5_AMOMAX
  | A64Instruction (Amominu_d rd rs1 rs2 aqrl) => mapper.(map_R_atomic) opcode_AMO rd rs1 rs2 funct3_AMOD aqrl funct5_AMOMINU
  | A64Instruction (Amomaxu_d rd rs1 rs2 aqrl) => mapper.(map_R_atomic) opcode_AMO rd rs1 rs2 funct3_AMOD aqrl funct5_AMOMAXU
  end.

Declare Scope z_bitwise_scope.
Notation "a <|> b" := (Z.lor a b) (at level 50, left associativity) : z_bitwise_scope.
Open Scope z_bitwise_scope.

Definition encode_Invalid(z: Z) := bitSlice z 0 32.

Definition encode_R(opcode: MachineInt)(rd rs1 rs2: Register)(funct3 funct7: MachineInt) :=
             (bitSlice opcode 0 7)    <|>
    Z.shiftl (bitSlice rd     0 5)  7 <|>
    Z.shiftl (bitSlice funct3 0 3) 12 <|>
    Z.shiftl (bitSlice rs1    0 5) 15 <|>
    Z.shiftl (bitSlice rs2    0 5) 20 <|>
    Z.shiftl (bitSlice funct7 0 7) 25.

Definition encode_R_atomic(opcode: MachineInt)(rd rs1 rs2: Register)(funct3 aqrl funct5: MachineInt) :=
             (bitSlice opcode 0 7)    <|>
    Z.shiftl (bitSlice rd     0 5)  7 <|>
    Z.shiftl (bitSlice funct3 0 3) 12 <|>
    Z.shiftl (bitSlice rs1    0 5) 15 <|>
    Z.shiftl (bitSlice rs2    0 5) 20 <|>
    Z.shiftl (bitSlice aqrl   0 2) 25 <|>
    Z.shiftl (bitSlice funct5 0 5) 27.

Definition encode_I(opcode: MachineInt)(rd rs1: Register)(funct3: MachineInt)(oimm12: Z) :=
             (bitSlice opcode 0  7)    <|>
    Z.shiftl (bitSlice rd     0  5)  7 <|>
    Z.shiftl (bitSlice funct3 0  3) 12 <|>
    Z.shiftl (bitSlice rs1    0  5) 15 <|>
    Z.shiftl (bitSlice oimm12 0 12) 20.

Definition encode_I_shift_57(opcode: MachineInt)(rd rs1: Register)(shamt5 funct3 funct7: MachineInt) :=
             (bitSlice opcode 0 7)    <|>
    Z.shiftl (bitSlice rd     0 5)  7 <|>
    Z.shiftl (bitSlice funct3 0 3) 12 <|>
    Z.shiftl (bitSlice rs1    0 5) 15 <|>
    Z.shiftl (bitSlice shamt5 0 5) 20 <|>
    Z.shiftl (bitSlice funct7 0 7) 25.

Definition encode_I_shift_66(opcode: MachineInt)(rd rs1: Register)(shamt6 funct3 funct6: MachineInt) :=
             (bitSlice opcode 0 7)    <|>
    Z.shiftl (bitSlice rd     0 5)  7 <|>
    Z.shiftl (bitSlice funct3 0 3) 12 <|>
    Z.shiftl (bitSlice rs1    0 5) 15 <|>
    Z.shiftl (bitSlice shamt6 0 6) 20 <|>
    Z.shiftl (bitSlice funct6 0 6) 26.

Definition encode_I_system(opcode: MachineInt)(rd rs1: Register)(funct3 funct12: MachineInt) :=
             (bitSlice opcode  0  7)    <|>
    Z.shiftl (bitSlice rd      0  5)  7 <|>
    Z.shiftl (bitSlice funct3  0  3) 12 <|>
    Z.shiftl (bitSlice rs1     0  5) 15 <|>
    Z.shiftl (bitSlice funct12 0 12) 20.

Definition encode_S(opcode: MachineInt)(rs1 rs2: Register)(funct3: MachineInt)(simm12: Z) :=
             (bitSlice opcode 0  7)    <|>
    Z.shiftl (bitSlice simm12 0  5)  7 <|>
    Z.shiftl (bitSlice funct3 0  3) 12 <|>
    Z.shiftl (bitSlice rs1    0  5) 15 <|>
    Z.shiftl (bitSlice rs2    0  5) 20 <|>
    Z.shiftl (bitSlice simm12 5 12) 25.

Definition encode_SB(opcode: MachineInt)(rs1 rs2: Register)(funct3: MachineInt)(sbimm12: Z) :=
             (bitSlice opcode   0  7)    <|>        (*  0..7  (7 bit) *)
    Z.shiftl (bitSlice sbimm12 11 12)  7 <|>        (*  7..8  (1 bit) *)
    Z.shiftl (bitSlice sbimm12  1  5)  8 <|>        (*  8..12 (4 bit) *)
    Z.shiftl (bitSlice funct3   0  3) 12 <|>        (* 12..15 (3 bit) *)
    Z.shiftl (bitSlice rs1      0  5) 15 <|>        (* 15..20 (5 bit) *)
    Z.shiftl (bitSlice rs2      0  5) 20 <|>        (* 20..25 (5 bit) *)
    Z.shiftl (bitSlice sbimm12  5 11) 25 <|>        (* 25..31 (6 bit) *)
    Z.shiftl (bitSlice sbimm12 12 13) 31.           (* 31..32 (1 bit) *)

Definition encode_U(opcode: MachineInt)(rd: Register)(imm20: Z) :=
             (bitSlice opcode 0  7)    <|>
    Z.shiftl (bitSlice rd     0  5)  7 <|>
    Z.shiftl (bitSlice imm20 12 32) 12.

Definition encode_UJ(opcode: MachineInt)(rd: Register)(jimm20: Z) :=
             (bitSlice opcode  0  7)    <|>
    Z.shiftl (bitSlice rd      0  5) 7 <|>
    Z.shiftl (bitSlice jimm20 12 20) 12 <|>
    Z.shiftl (bitSlice jimm20 11 12) 20 <|>
    Z.shiftl (bitSlice jimm20  1 11) 21 <|>
    Z.shiftl (bitSlice jimm20 20 21) 31.

Definition encode_Fence(opcode: MachineInt)(rd rs1: Register)(funct3 prd scc msb4: MachineInt) :=
             (bitSlice opcode 0 7)    <|>             (*  0..7  (7 bit) *)
    Z.shiftl (bitSlice rd     0 5)  7 <|>             (*  7..12 (5 bit) *)
    Z.shiftl (bitSlice funct3 0 3) 12 <|>             (* 12..15 (3 bit) *)
    Z.shiftl (bitSlice rs1    0 5) 15 <|>             (* 15..20 (5 bit) *)
    Z.shiftl (bitSlice scc    0 4) 20 <|>             (* 20..24 (4 bit) *)
    Z.shiftl (bitSlice prd    0 4) 24 <|>             (* 24..28 (4 bit) *)
    Z.shiftl (bitSlice msb4   0 4) 28.                (* 28..32 (4 bit) *)

Definition encode_FenceI(opcode: MachineInt)(rd rs1: Register)(funct3 imm12: MachineInt) :=
             (bitSlice opcode 0  7)    <|>             (*  0..7  ( 7 bit) *)
    Z.shiftl (bitSlice rd     0  5)  7 <|>             (*  7..12 ( 5 bit) *)
    Z.shiftl (bitSlice funct3 0  3) 12 <|>             (* 12..15 ( 3 bit) *)
    Z.shiftl (bitSlice rs1    0  5) 15 <|>             (* 15..20 ( 5 bit) *)
    Z.shiftl (bitSlice imm12  0 12) 20.                (* 20..32 (12 bit) *)

Definition Encoder: InstructionMapper MachineInt := {|
  map_Invalid := encode_Invalid;
  map_R := encode_R;
  map_R_atomic := encode_R_atomic;
  map_I := encode_I;
  map_I_shift_57 := encode_I_shift_57;
  map_I_shift_66 := encode_I_shift_66;
  map_I_system := encode_I_system;
  map_S := encode_S;
  map_SB := encode_SB;
  map_U := encode_U;
  map_UJ := encode_UJ;
  map_Fence := encode_Fence;
  map_FenceI := encode_FenceI;
|}.

Definition encode: Instruction -> MachineInt := apply_InstructionMapper Encoder.

#[export] Hint Unfold
  encode
  encode_Fence
  encode_I
  encode_Invalid
  encode_I_shift_57
  encode_I_shift_66
  encode_I_system
  encode_R
  encode_R_atomic
  encode_S
  encode_SB
  encode_U
  encode_UJ
: encoders.


Definition verify_Invalid(i: Z) :=
    False.

Definition verify_R(opcode: MachineInt)(rd rs1 rs2: Register)(funct3 funct7: MachineInt) :=
    0 <= opcode < 2^7 /\
    0 <= rd     < 2^5 /\
    0 <= rs1    < 2^5 /\
    0 <= rs2    < 2^5 /\
    0 <= funct3 < 2^3 /\
    0 <= funct7 < 2^7 .

Definition verify_R_atomic(opcode: MachineInt)(rd rs1 rs2: Register)(funct3 aqrl funct5: MachineInt) :=
    0 <= opcode < 2^7 /\
    0 <= rd     < 2^5 /\
    0 <= rs1    < 2^5 /\
    0 <= rs2    < 2^5 /\
    0 <= funct3 < 2^3 /\
    0 <= aqrl   < 2^2 /\
    0 <= funct5 < 2^5 .

Definition verify_I(opcode: MachineInt)(rd rs1: Register)(funct3: MachineInt)(oimm12: Z) :=
    0 <= opcode < 2^7 /\
    0 <= rd     < 2^5 /\
    0 <= rs1    < 2^5 /\
    0 <= funct3 < 2^3 /\
    - 2^11 <= oimm12 < 2^11.

Definition verify_I_shift_57(opcode: MachineInt)(rd rs1: Register)(shamt5 funct3 funct7: MachineInt) :=
    0 <= opcode < 2^7 /\
    0 <= rd     < 2^5 /\
    0 <= rs1    < 2^5 /\
    0 <= shamt5 < 2^5 /\
    0 <= funct3 < 2^3 /\
    0 <= funct7 < 2^7 .

Definition verify_I_shift_66(bitwidth: Z)(opcode: MachineInt)(rd rs1: Register)(shamt6 funct3 funct6: MachineInt) :=
    0 <= opcode < 2^7 /\
    0 <= rd     < 2^5 /\
    0 <= rs1    < 2^5 /\
    0 <= shamt6 < bitwidth /\ (bitwidth = 2^5 \/ bitwidth = 2^6) /\
    0 <= funct3 < 2^3 /\
    0 <= funct6 < 2^6 .

Definition verify_I_system(opcode: MachineInt)(rd rs1: Register)(funct3 funct12: MachineInt) :=
    0 <= opcode  < 2^7 /\
    0 <= rd      < 2^5 /\
    0 <= rs1     < 2^5 /\
    0 <= funct3  < 2^3 /\
    0 <= funct12 < 2^12 .

Definition verify_S(opcode: MachineInt)(rs1 rs2: Register)(funct3: MachineInt)(simm12: Z) :=
    0 <= opcode < 2^7 /\
    0 <= rs1    < 2^5 /\
    0 <= rs2    < 2^5 /\
    0 <= funct3 < 2^3 /\
    - 2^11 <= simm12 < 2^11.

Definition verify_SB(opcode: MachineInt)(rs1 rs2: Register)(funct3: MachineInt)(sbimm12: Z) :=
    0 <= opcode < 2^7 /\
    0 <= rs1    < 2^5 /\
    0 <= rs2    < 2^5 /\
    0 <= funct3 < 2^3 /\
    - 2^12 <= sbimm12 < 2^12 /\ sbimm12 mod 2 = 0.

Definition verify_U(opcode: MachineInt)(rd: Register)(imm20: Z) :=
    0 <= opcode < 2^7 /\
    0 <= rd     < 2^5 /\
    - 2^31 <= imm20 < 2^31 /\ imm20 mod 2^12 = 0.

Definition verify_UJ(opcode: MachineInt)(rd: Register)(jimm20: Z) :=
    0 <= opcode < 2^7 /\
    0 <= rd     < 2^5 /\
    - 2^20 <= jimm20 < 2^20 /\ jimm20 mod 2 = 0.

Definition verify_Fence(opcode: MachineInt)(rd rs1: Register)(funct3 prd scc msb4: MachineInt) :=
    0 <= opcode < 2^7 /\
    0 <= rd     < 2^5 /\
    0 <= rs1    < 2^5 /\
    0 <= funct3 < 2^3 /\
    0 <= prd    < 2^4 /\
    0 <= scc    < 2^4 /\
    0 <= msb4   < 2^4 .

Definition verify_FenceI(opcode: MachineInt)(rd rs1: Register)(funct3 imm12: MachineInt) :=
    0 <= opcode < 2^7 /\
    0 <= rd     < 2^5 /\
    0 <= rs1    < 2^5 /\
    0 <= funct3 < 2^3 /\
    - 2^11 <= imm12 < 2^11.

(* Only verifies that each field is within bounds and has the correct modulus.
   Validity of opcodes and funct codes follows from the fact that it was an Instruction. *)
Definition Verifier(bitwidth: Z): InstructionMapper Prop := {|
  map_Invalid := verify_Invalid;
  map_R := verify_R;
  map_R_atomic := verify_R_atomic;
  map_I := verify_I;
  map_I_shift_57 := verify_I_shift_57;
  map_I_shift_66 := verify_I_shift_66 bitwidth;
  map_I_system := verify_I_system;
  map_S := verify_S;
  map_SB := verify_SB;
  map_U := verify_U;
  map_UJ := verify_UJ;
  map_Fence := verify_Fence;
  map_FenceI := verify_FenceI;
|}.

Definition respects_bounds(bitwidth: Z): Instruction -> Prop :=
  apply_InstructionMapper (Verifier bitwidth).

(* We don't use F and F64, so we return False for them so that they don't complicate the
   decode_encode proof, and we don't allow any RV..F.. in the rhs *)
Definition verify_iset(inst: Instruction)(iset: InstructionSet): Prop :=
  match inst with
  | IInstruction i => True
  | MInstruction i => iset = RV32IM \/ iset = RV32IMA \/ iset = RV64IM \/ iset = RV64IMA
  | AInstruction i => iset = RV32IA \/ iset = RV32IMA \/ iset = RV64IA \/ iset = RV64IMA
  | FInstruction i => False
  | I64Instruction i => iset = RV64I \/ iset = RV64IM \/ iset = RV64IA \/ iset = RV64IMA
  | M64Instruction i =>                 iset = RV64IM \/                  iset = RV64IMA
  | A64Instruction i =>                                  iset = RV64IA \/ iset = RV64IMA
  | F64Instruction i => False
  | CSRInstruction i => True
  | InvalidInstruction _ => False
  end.

Definition verify(inst: Instruction)(iset: InstructionSet): Prop :=
  respects_bounds (bitwidth iset) inst /\ verify_iset inst iset.

#[global] Hint Unfold
  map_Invalid
  map_R
  map_R_atomic
  map_I
  map_I_shift_57
  map_I_shift_66
  map_I_system
  map_S
  map_SB
  map_U
  map_UJ
  map_Fence
  map_FenceI
  Verifier
  Encoder
  apply_InstructionMapper
: mappers.

Goal (respects_bounds 32 (IInstruction (Jal 0 3))).
  simpl. unfold verify_UJ.
  (* wrong, as expected *)
Abort.

Require Import coqutil.Z.Lia.

Goal (respects_bounds 32 (IInstruction (Jal 0 4))).
  simpl. unfold verify_UJ.
  unfold opcode_JAL.
  cbn.
  blia.
Qed.

(* This expression will generate a runtime exception, because the jump target is not
   a multiple of 4 *)
Example invalid_Jal_encode_example: encode (IInstruction (Jal 0 3)) = 0x20006F. reflexivity. Qed.

(* Note: The least significant bit of the jump target is not encoded, because even
   in compressed instructions, jump targets are always a multiple of 2. *)
Example Jal_encode_loses_lsb: decode RV64IM (0x20006F) = IInstruction (Jal 0 2). reflexivity. Qed.
