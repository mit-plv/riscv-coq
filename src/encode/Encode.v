(* Need to define Register *)
Require Import Coq.omega.Omega.
Require Import bbv.WordScope.
Require Import bbv.BinNotationZ.
Require Import riscv.RiscvBitWidths.
Require Import riscv.Decode.
Require Import riscv.util.NameWithEq.
Require Import riscv.Utility.


Definition funct3_JALR := Ob"000". (* TODO why does Decode not define & check this? *)

Local Open Scope Z_scope.

Definition Register := Z.

Record InstructionMapper{T: Type} := mkInstructionMapper {
  map_Invalid: T;
  map_R(opcode: MachineInt)(rd rs1 rs2: Register)(funct3: MachineInt)(funct7: MachineInt): T;
  map_I(opcode: MachineInt)(rd rs1: Register)(funct3: MachineInt)(oimm12: Z): T;
  map_I_shift(opcode: MachineInt)(rd rs1: Register)(shamt5 funct3 funct7: MachineInt): T;
  map_I_system(opcode: MachineInt)(rd rs1: Register)(funct3 funct12: MachineInt): T;
  map_S(opcode: MachineInt)(rs1 rs2: Register)(funct3: MachineInt)(simm12: Z): T;
  map_SB(opcode: MachineInt)(rs1 rs2: Register)(funct3: MachineInt)(sbimm12: Z): T;
  map_U(opcode: MachineInt)(rd: Register)(imm20: Z): T;
  map_UJ(opcode: MachineInt)(rd: Register)(jimm20: Z): T;
  map_Fence(opcode: MachineInt)(rd rs1: Register)(funct3: MachineInt)(prd scc msb4: MachineInt): T;
}.

Arguments InstructionMapper: clear implicits.


Local Instance ZName: NameWithEq := {|
  name := Z
|}.

Definition apply_InstructionMapper{T: Type}(mapper: InstructionMapper T)
  (inst: @Instruction ZName): T :=
  match inst with
  | InvalidInstruction => mapper.(map_Invalid)

  | Lb  rd rs1 oimm12 => mapper.(map_I) opcode_LOAD rd rs1 funct3_LB  oimm12
  | Lh  rd rs1 oimm12 => mapper.(map_I) opcode_LOAD rd rs1 funct3_LH  oimm12
  | Lw  rd rs1 oimm12 => mapper.(map_I) opcode_LOAD rd rs1 funct3_LW  oimm12
  | Ld  rd rs1 oimm12 => mapper.(map_I) opcode_LOAD rd rs1 funct3_LD  oimm12
  | Lbu rd rs1 oimm12 => mapper.(map_I) opcode_LOAD rd rs1 funct3_LBU oimm12
  | Lhu rd rs1 oimm12 => mapper.(map_I) opcode_LOAD rd rs1 funct3_LHU oimm12
  | Lwu rd rs1 oimm12 => mapper.(map_I) opcode_LOAD rd rs1 funct3_LWU oimm12

  | Fence pred succ => mapper.(map_Fence) opcode_MISC_MEM 0 0 funct3_FENCE pred succ 0
  | Fence_i =>         mapper.(map_Fence) opcode_MISC_MEM 0 0 funct3_FENCE_I 0 0 0

  | Addi  rd rs1 imm12  => mapper.(map_I) opcode_OP_IMM rd rs1 funct3_ADDI imm12
  | Slli  rd rs1 shamt5 => mapper.(map_I_shift) opcode_OP_IMM rd rs1 shamt5 funct3_SLLI funct7_SLLI
  | Slti  rd rs1 imm12  => mapper.(map_I) opcode_OP_IMM rd rs1 funct3_SLTI imm12
  | Sltiu rd rs1 imm12  => mapper.(map_I) opcode_OP_IMM rd rs1 funct3_SLTIU imm12
  | Xori  rd rs1 imm12  => mapper.(map_I) opcode_OP_IMM rd rs1 funct3_XORI imm12
  | Ori   rd rs1 imm12  => mapper.(map_I) opcode_OP_IMM rd rs1 funct3_ORI imm12
  | Andi  rd rs1 imm12  => mapper.(map_I) opcode_OP_IMM rd rs1 funct3_ANDI imm12
  | Srli  rd rs1 shamt5 => mapper.(map_I_shift) opcode_OP_IMM rd rs1 shamt5 funct3_SRLI funct7_SRLI
  | Srai  rd rs1 shamt5 => mapper.(map_I_shift) opcode_OP_IMM rd rs1 shamt5 funct3_SRAI funct7_SRAI

  | Auipc rd oimm20 => mapper.(map_U) opcode_AUIPC rd oimm20

  | Addiw rd rs1 imm12 => mapper.(map_I) opcode_OP_IMM_32 rd rs1 funct3_ADDIW imm12
  | Slliw rd rs1 shm5  => mapper.(map_I_shift) opcode_OP_IMM_32 rd rs1 shm5 funct3_SLLI funct7_SLLI
  | Srliw rd rs1 shm5  => mapper.(map_I_shift) opcode_OP_IMM_32 rd rs1 shm5 funct3_SRLI funct7_SRLI
  | Sraiw rd rs1 shm5  => mapper.(map_I_shift) opcode_OP_IMM_32 rd rs1 shm5 funct3_SRAI funct7_SRAI

  | Sb rs1 rs2 simm12 => mapper.(map_S) opcode_STORE rs1 rs2 funct3_SB simm12
  | Sh rs1 rs2 simm12 => mapper.(map_S) opcode_STORE rs1 rs2 funct3_SH simm12
  | Sw rs1 rs2 simm12 => mapper.(map_S) opcode_STORE rs1 rs2 funct3_SW simm12
  | Sd rs1 rs2 simm12 => mapper.(map_S) opcode_STORE rs1 rs2 funct3_SD simm12

  | Add    rd rs1 rs2 => mapper.(map_R) opcode_OP rd rs1 rs2 funct3_ADD    funct7_ADD
  | Sub    rd rs1 rs2 => mapper.(map_R) opcode_OP rd rs1 rs2 funct3_SUB    funct7_SUB
  | Sll    rd rs1 rs2 => mapper.(map_R) opcode_OP rd rs1 rs2 funct3_SLL    funct7_SLL
  | Slt    rd rs1 rs2 => mapper.(map_R) opcode_OP rd rs1 rs2 funct3_SLT    funct7_SLT
  | Sltu   rd rs1 rs2 => mapper.(map_R) opcode_OP rd rs1 rs2 funct3_SLTU   funct7_SLTU
  | Xor    rd rs1 rs2 => mapper.(map_R) opcode_OP rd rs1 rs2 funct3_XOR    funct7_XOR
  | Srl    rd rs1 rs2 => mapper.(map_R) opcode_OP rd rs1 rs2 funct3_SRL    funct7_SRL
  | Sra    rd rs1 rs2 => mapper.(map_R) opcode_OP rd rs1 rs2 funct3_SRA    funct7_SRA
  | Or     rd rs1 rs2 => mapper.(map_R) opcode_OP rd rs1 rs2 funct3_OR     funct7_OR
  | And    rd rs1 rs2 => mapper.(map_R) opcode_OP rd rs1 rs2 funct3_AND    funct7_AND
  | Mul    rd rs1 rs2 => mapper.(map_R) opcode_OP rd rs1 rs2 funct3_MUL    funct7_MUL
  | Mulh   rd rs1 rs2 => mapper.(map_R) opcode_OP rd rs1 rs2 funct3_MULH   funct7_MULH
  | Mulhsu rd rs1 rs2 => mapper.(map_R) opcode_OP rd rs1 rs2 funct3_MULHSU funct7_MULHSU
  | Mulhu  rd rs1 rs2 => mapper.(map_R) opcode_OP rd rs1 rs2 funct3_MULHU  funct7_MULHU
  | Div    rd rs1 rs2 => mapper.(map_R) opcode_OP rd rs1 rs2 funct3_DIV    funct7_DIV
  | Divu   rd rs1 rs2 => mapper.(map_R) opcode_OP rd rs1 rs2 funct3_DIVU   funct7_DIVU
  | Rem    rd rs1 rs2 => mapper.(map_R) opcode_OP rd rs1 rs2 funct3_REM    funct7_REM
  | Remu   rd rs1 rs2 => mapper.(map_R) opcode_OP rd rs1 rs2 funct3_REMU   funct7_REMU

  | Lui rd imm20 => mapper.(map_U) opcode_LUI rd imm20

  | Addw  rd rs1 rs2 => mapper.(map_R) opcode_OP rd rs1 rs2 funct3_ADDW  funct7_ADDW
  | Subw  rd rs1 rs2 => mapper.(map_R) opcode_OP rd rs1 rs2 funct3_SUBW  funct7_SUBW
  | Sllw  rd rs1 rs2 => mapper.(map_R) opcode_OP rd rs1 rs2 funct3_SLLW  funct7_SLLW
  | Srlw  rd rs1 rs2 => mapper.(map_R) opcode_OP rd rs1 rs2 funct3_SRLW  funct7_SRLW
  | Sraw  rd rs1 rs2 => mapper.(map_R) opcode_OP rd rs1 rs2 funct3_SRAW  funct7_SRAW
  | Mulw  rd rs1 rs2 => mapper.(map_R) opcode_OP rd rs1 rs2 funct3_MULW  funct7_MULW
  | Divw  rd rs1 rs2 => mapper.(map_R) opcode_OP rd rs1 rs2 funct3_DIVW  funct7_DIVW
  | Divuw rd rs1 rs2 => mapper.(map_R) opcode_OP rd rs1 rs2 funct3_DIVUW funct7_DIVUW
  | Remw  rd rs1 rs2 => mapper.(map_R) opcode_OP rd rs1 rs2 funct3_REMW  funct7_REMW
  | Remuw rd rs1 rs2 => mapper.(map_R) opcode_OP rd rs1 rs2 funct3_REMUW funct7_REMUW

  | Beq  rs1 rs2 sbimm12 => mapper.(map_SB) opcode_BRANCH rs1 rs2 funct3_BEQ  sbimm12
  | Bne  rs1 rs2 sbimm12 => mapper.(map_SB) opcode_BRANCH rs1 rs2 funct3_BNE  sbimm12
  | Blt  rs1 rs2 sbimm12 => mapper.(map_SB) opcode_BRANCH rs1 rs2 funct3_BLT  sbimm12
  | Bge  rs1 rs2 sbimm12 => mapper.(map_SB) opcode_BRANCH rs1 rs2 funct3_BGE  sbimm12
  | Bltu rs1 rs2 sbimm12 => mapper.(map_SB) opcode_BRANCH rs1 rs2 funct3_BLTU sbimm12
  | Bgeu rs1 rs2 sbimm12 => mapper.(map_SB) opcode_BRANCH rs1 rs2 funct3_BGEU sbimm12

  | Jalr rd rs1 oimm12 => mapper.(map_I) opcode_JALR rd rs1 funct3_JALR oimm12
  | Jal rd jimm20 => mapper.(map_UJ) opcode_JAL rd jimm20

  | Ecall  => mapper.(map_I_system) opcode_SYSTEM 0 0 funct3_PRIV funct12_ECALL
  | Ebreak => mapper.(map_I_system) opcode_SYSTEM 0 0 funct3_PRIV funct12_EBREAK
  | Uret   => mapper.(map_I_system) opcode_SYSTEM 0 0 funct3_PRIV funct12_URET
  | Sret   => mapper.(map_I_system) opcode_SYSTEM 0 0 funct3_PRIV funct12_SRET
  | Mret   => mapper.(map_I_system) opcode_SYSTEM 0 0 funct3_PRIV funct12_MRET
  | Wfi    => mapper.(map_I_system) opcode_SYSTEM 0 0 funct3_PRIV funct12_WFI

  | Sfence_vm rs1 rs2 => mapper.(map_R) opcode_SYSTEM 0 rs1 rs2 funct3_PRIV funct7_SFENCE_VM

  | Csrrw  rd rs1  csr12 => mapper.(map_I_system) opcode_SYSTEM rd rs1  funct3_CSRRW  csr12
  | Csrrs  rd rs1  csr12 => mapper.(map_I_system) opcode_SYSTEM rd rs1  funct3_CSRRS  csr12
  | Csrrc  rd rs1  csr12 => mapper.(map_I_system) opcode_SYSTEM rd rs1  funct3_CSRRC  csr12
  | Csrrwi rd zimm csr12 => mapper.(map_I_system) opcode_SYSTEM rd zimm funct3_CSRRWI csr12
  | Csrrsi rd zimm csr12 => mapper.(map_I_system) opcode_SYSTEM rd zimm funct3_CSRRSI csr12
  | Csrrci rd zimm csr12 => mapper.(map_I_system) opcode_SYSTEM rd zimm funct3_CSRRCI csr12
  end.


Definition Encoder: InstructionMapper MachineInt := {|
  map_Invalid := 0; (* all zeroes is indeed an invalid expression *)

  map_R(opcode: MachineInt)(rd rs1 rs2: Register)(funct3: MachineInt)(funct7: MachineInt) :=
    opcode <|>
    shift rd 7 <|>
    shift funct3 12 <|>
    shift rs1 15 <|>
    shift rs2 20 <|>
    shift funct7 25;

  map_I(opcode: MachineInt)(rd rs1: Register)(funct3: MachineInt)(oimm12: Z) :=
    opcode <|>
    shift rd 7 <|>
    shift funct3 12 <|>
    shift rs1 15 <|>
    shift oimm12 20;

  map_I_shift(opcode: MachineInt)(rd rs1: Register)(shamt5 funct3 funct7: MachineInt) := 
    opcode <|>
    shift rd 7 <|>
    shift funct3 12 <|>
    shift rs1 15 <|>
    shift shamt5 20 <|>
    shift funct7 25;

  map_I_system(opcode: MachineInt)(rd rs1: Register)(funct3 funct12: MachineInt) :=
    opcode <|>
    shift rd 7 <|>
    shift funct3 12 <|>
    shift rs1 15 <|>
    shift funct12 20;

  map_S(opcode: MachineInt)(rs1 rs2: Register)(funct3: MachineInt)(simm12: Z) :=
    opcode <|>
    shift (bitSlice simm12 0 5) 7 <|>
    shift funct3 12 <|>
    shift rs1 15 <|>
    shift rs2 20 <|>
    shift (bitSlice simm12 5 12) 25;

  map_SB(opcode: MachineInt)(rs1 rs2: Register)(funct3: MachineInt)(sbimm12: Z) :=
    opcode <|>                                   (*  0..7  (7 bit) *)
    shift (bitSlice sbimm12 11 12) 7 <|>         (*  7..8  (1 bit) *)
    shift (bitSlice sbimm12 1 5) 8 <|>           (*  8..12 (4 bit) *)
    shift funct3 12 <|>                          (* 12..15 (3 bit) *)
    shift rs1 15 <|>                             (* 15..20 (5 bit) *)
    shift rs2 20 <|>                             (* 20..25 (5 bit) *)
    shift (bitSlice sbimm12 5 11) 25 <|>         (* 25..31 (6 bit) *)
    shift (bitSlice sbimm12 12 13) 31;           (* 31..32 (1 bit) *)

  map_U(opcode: MachineInt)(rd: Register)(imm20: Z) :=
    opcode <|>
    shift rd 7 <|>
    imm20;

  map_UJ(opcode: MachineInt)(rd: Register)(jimm20: Z) :=
    opcode <|>
    shift rd 7 <|>
    shift (bitSlice jimm20 12 20) 12 <|>
    shift (bitSlice jimm20 11 12) 20 <|>
    shift (bitSlice jimm20 1 11) 21 <|>
    shift (bitSlice jimm20 20 21) 31;

  map_Fence(opcode: MachineInt)(rd rs1: Register)(funct3: MachineInt)(prd scc msb4: MachineInt) :=
    opcode <|>                                (*  0..7  (7 bit) *)
    shift rd 7 <|>                            (*  7..12 (5 bit) *)
    shift funct3 12 <|>                       (* 12..15 (3 bit) *)
    shift rs1 15 <|>                          (* 15..20 (5 bit) *)
    shift scc 20 <|>                          (* 20..24 (4 bit) *)
    shift prd 24 <|>                          (* 24..28 (4 bit) *)
    shift msb4 28;                            (* 28..32 (4 bit) *)
|}.

