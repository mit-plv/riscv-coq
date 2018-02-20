(* Need to define MachineInt = Int64? Int32 *)
(* Need to define Register *)
Require Import Coq.Bool.Sumbool.
Require Import Coq.omega.Omega.
Require Import bbv.WordScope.
Require Import riscv.util.Decidable.
Require Import bbv.DepEqNat.
Require Import riscv.RiscvBitWidths.
Require Import riscv.Decode.

Definition funct3_JALR := WO~0~0~0. (* TODO why does Decode not define & check this? *)

Local Notation "upper ++ lower" := (combine lower upper) (right associativity, at level 60).

Local Open Scope Z_scope.

Definition encode_R(opcode: word 7)(rd rs1 rs2: word 5)(funct3: word 3)(funct7: word 7)
 : option (word 32) := Some (funct7 ++ rs2 ++ rs1 ++ funct3 ++ rd ++ opcode).

Definition encode_I(opcode: word 7)(rd rs1: word 5)(funct3: word 3)(oimm12: Z): option (word 32) :=
  if dec (- 2 ^ 11 <= oimm12 < 2 ^ 11)
  then Some ((ZToWord 12 oimm12) ++ rs1 ++ funct3 ++ rd ++ opcode)
  else None.

Definition encode_I_shift(opcode: word 7)(rd rs1: word 5)(shamt5: nat)(funct3: word 3)
  (funct7: word 7) : option (word 32) := 
  if dec (shamt5 < 32)%nat
  then Some (funct7 ++ (natToWord 5 shamt5) ++ rs1 ++ funct3 ++ rd ++ opcode)
  else None.

Definition encode_I_system(opcode: word 7)(rd rs1: word 5)(funct3: word 3)(funct12: word 12)
  : option (word 32) := Some (funct12 ++ rs1 ++ funct3 ++ rd ++ opcode).

Definition encode_S(opcode: word 7)(rs1 rs2: word 5)(funct3: word 3)(simm12: Z): option (word 32) :=
  if dec (- 2 ^ 11 <= simm12 < 2 ^ 11)
  then
    let w := ZToWord 12 simm12 in
    Some ((split_upper 7 5 w) ++ rs2 ++ rs1 ++ funct3 ++ (split_lower 7 5 w) ++ opcode)
  else None.

Definition encode_SB(opcode: word 7)(rs1 rs2: word 5)(funct3: word 3)(sbimm12: Z):
  option (word 32) :=
  if dec (- 2 ^ 12 <= sbimm12 < 2 ^ 12 /\ sbimm12 mod 2 = 0)
  then
    let w := ZToWord 13 sbimm12 in
    Some ((split_upper 1 12 w) ++ (split_middle 2 6 5 w) ++ rs2 ++ rs1 ++ funct3 ++ 
          (split_middle 8 4 1 w) ++ (split_middle 1 1 11 w) ++ opcode)
  else None.

Definition encode_U(opcode: word 7)(rd: word 5)(imm20: Z): option (word 32) :=
  if dec (- 2 ^ 31 <= imm20 < 2 ^ 31 /\ imm20 mod 2 ^ 12 = 0)
  then Some ((split_upper 20 12 (ZToWord 32 imm20)) ++ rd ++ opcode)
  else None.

Definition encode_UJ(opcode: word 7)(rd: word 5)(jimm20: Z): option (word 32) :=
  if dec (- 2 ^ 20 <= jimm20 < 2 ^ 20 /\ jimm20 mod 2 = 0)
  then
    let w := ZToWord 21 jimm20 in
    Some ((split_upper 1 20 w) ++ (split_middle 10 10 1 w) ++ (split_middle 9 1 11 w) ++
          (split_middle 1 8 12 w) ++ rd ++ opcode)
  else None.

Definition encode(inst: Instruction): option (word 32) := match inst with
  | InvalidInstruction => None

  | Lb  rd rs1 oimm12 => encode_I opcode_LOAD rd rs1 funct3_LB  oimm12
  | Lh  rd rs1 oimm12 => encode_I opcode_LOAD rd rs1 funct3_LH  oimm12
  | Lw  rd rs1 oimm12 => encode_I opcode_LOAD rd rs1 funct3_LW  oimm12
  | Ld  rd rs1 oimm12 => encode_I opcode_LOAD rd rs1 funct3_LD  oimm12
  | Lbu rd rs1 oimm12 => encode_I opcode_LOAD rd rs1 funct3_LBU oimm12
  | Lhu rd rs1 oimm12 => encode_I opcode_LOAD rd rs1 funct3_LHU oimm12
  | Lwu rd rs1 oimm12 => encode_I opcode_LOAD rd rs1 funct3_LWU oimm12

  | Addi  rd rs1 imm12  => encode_I opcode_OP_IMM rd rs1 funct3_ADDI imm12
  | Slli  rd rs1 shamt5 => encode_I_shift opcode_OP_IMM rd rs1 shamt5 funct3_SLLI funct7_SLLI
  | Slti  rd rs1 imm12  => encode_I opcode_OP_IMM rd rs1 funct3_SLTI imm12
  | Sltiu rd rs1 imm12  => encode_I opcode_OP_IMM rd rs1 funct3_SLTIU imm12
  | Xori  rd rs1 imm12  => encode_I opcode_OP_IMM rd rs1 funct3_XORI imm12
  | Ori   rd rs1 imm12  => encode_I opcode_OP_IMM rd rs1 funct3_ORI imm12
  | Andi  rd rs1 imm12  => encode_I opcode_OP_IMM rd rs1 funct3_ANDI imm12
  | Srli  rd rs1 shamt5 => encode_I_shift opcode_OP_IMM rd rs1 shamt5 funct3_SRLI funct7_SRLI
  | Srai  rd rs1 shamt5 => encode_I_shift opcode_OP_IMM rd rs1 shamt5 funct3_SRAI funct7_SRAI

  | Auipc rd oimm20 => encode_U opcode_AUIPC rd oimm20

  | Sb rs1 rs2 simm12 => encode_S opcode_STORE rs1 rs2 funct3_SB simm12
  | Sh rs1 rs2 simm12 => encode_S opcode_STORE rs1 rs2 funct3_SH simm12
  | Sw rs1 rs2 simm12 => encode_S opcode_STORE rs1 rs2 funct3_SW simm12
  | Sd rs1 rs2 simm12 => encode_S opcode_STORE rs1 rs2 funct3_SD simm12

  | Add    rd rs1 rs2 => encode_R opcode_OP rd rs1 rs2 funct3_ADD    funct7_ADD
  | Sub    rd rs1 rs2 => encode_R opcode_OP rd rs1 rs2 funct3_SUB    funct7_SUB
  | Sll    rd rs1 rs2 => encode_R opcode_OP rd rs1 rs2 funct3_SLL    funct7_SLL
  | Slt    rd rs1 rs2 => encode_R opcode_OP rd rs1 rs2 funct3_SLT    funct7_SLT
  | Sltu   rd rs1 rs2 => encode_R opcode_OP rd rs1 rs2 funct3_SLTU   funct7_SLTU
  | Xor    rd rs1 rs2 => encode_R opcode_OP rd rs1 rs2 funct3_XOR    funct7_XOR
  | Srl    rd rs1 rs2 => encode_R opcode_OP rd rs1 rs2 funct3_SRL    funct7_SRL
  | Sra    rd rs1 rs2 => encode_R opcode_OP rd rs1 rs2 funct3_SRA    funct7_SRA
  | Or     rd rs1 rs2 => encode_R opcode_OP rd rs1 rs2 funct3_OR     funct7_OR
  | And    rd rs1 rs2 => encode_R opcode_OP rd rs1 rs2 funct3_AND    funct7_AND
  | Mul    rd rs1 rs2 => encode_R opcode_OP rd rs1 rs2 funct3_MUL    funct7_MUL
  | Mulh   rd rs1 rs2 => encode_R opcode_OP rd rs1 rs2 funct3_MULH   funct7_MULH
  | Mulhsu rd rs1 rs2 => encode_R opcode_OP rd rs1 rs2 funct3_MULHSU funct7_MULHSU
  | Mulhu  rd rs1 rs2 => encode_R opcode_OP rd rs1 rs2 funct3_MULHU  funct7_MULHU
  | Div    rd rs1 rs2 => encode_R opcode_OP rd rs1 rs2 funct3_DIV    funct7_DIV
  | Divu   rd rs1 rs2 => encode_R opcode_OP rd rs1 rs2 funct3_DIVU   funct7_DIVU
  | Rem    rd rs1 rs2 => encode_R opcode_OP rd rs1 rs2 funct3_REM    funct7_REM
  | Remu   rd rs1 rs2 => encode_R opcode_OP rd rs1 rs2 funct3_REMU   funct7_REMU

  | Lui rd imm20 => encode_U opcode_LUI rd imm20

  | Beq  rs1 rs2 sbimm12 => encode_SB opcode_BRANCH rs1 rs2 funct3_BEQ  sbimm12
  | Bne  rs1 rs2 sbimm12 => encode_SB opcode_BRANCH rs1 rs2 funct3_BNE  sbimm12
  | Blt  rs1 rs2 sbimm12 => encode_SB opcode_BRANCH rs1 rs2 funct3_BLT  sbimm12
  | Bge  rs1 rs2 sbimm12 => encode_SB opcode_BRANCH rs1 rs2 funct3_BGE  sbimm12
  | Bltu rs1 rs2 sbimm12 => encode_SB opcode_BRANCH rs1 rs2 funct3_BLTU sbimm12
  | Bgeu rs1 rs2 sbimm12 => encode_SB opcode_BRANCH rs1 rs2 funct3_BGEU sbimm12

  | Jalr rd rs1 oimm12 => encode_I opcode_JALR rd rs1 funct3_JALR oimm12
  | Jal rd jimm20 => encode_UJ opcode_JAL rd jimm20

  | Ecall  => encode_I_system opcode_SYSTEM $0 $0 funct3_PRIV funct12_ECALL
  | Ebreak => encode_I_system opcode_SYSTEM $0 $0 funct3_PRIV funct12_EBREAK
  | Uret   => encode_I_system opcode_SYSTEM $0 $0 funct3_PRIV funct12_URET
  | Sret   => encode_I_system opcode_SYSTEM $0 $0 funct3_PRIV funct12_SRET
  | Mret   => encode_I_system opcode_SYSTEM $0 $0 funct3_PRIV funct12_MRET
  | Wfi    => encode_I_system opcode_SYSTEM $0 $0 funct3_PRIV funct12_WFI

  | Csrrw  rd rs1  csr12 => encode_I_system opcode_SYSTEM rd rs1  funct3_CSRRW  csr12
  | Csrrs  rd rs1  csr12 => encode_I_system opcode_SYSTEM rd rs1  funct3_CSRRS  csr12
  | Csrrc  rd rs1  csr12 => encode_I_system opcode_SYSTEM rd rs1  funct3_CSRRC  csr12
  | Csrrwi rd zimm csr12 => encode_I_system opcode_SYSTEM rd zimm funct3_CSRRWI csr12
  | Csrrsi rd zimm csr12 => encode_I_system opcode_SYSTEM rd zimm funct3_CSRRSI csr12
  | Csrrci rd zimm csr12 => encode_I_system opcode_SYSTEM rd zimm funct3_CSRRCI csr12
  end.
