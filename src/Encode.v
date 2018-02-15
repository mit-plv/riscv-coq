(* Need to define MachineInt = Int64? Int32 *)
(* Need to define Register *)
Require Import Coq.Bool.Sumbool.
Require Import Coq.omega.Omega.
Require Import bbv.WordScope.
Require Import riscv.Decidable.
Require Import bbv.DepEqNat.
Require Import riscv.RiscvBitWidths.
Require Import riscv.Decode.

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

  | Fence_i => encode_I opcode_MISC_MEM $0 $0 funct3_FENCE_I 0

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

  (* TODO (these are 64bit only) *)
  | Addiw rd rs1 imm12 => None
  | Slliw rd rs1 shamt5 => None
  | Srliw rd rs1 shamt5 => None
  | Sraiw rd rs1 shamt5 => None

  | Sb rs1 rs2 simm12 => encode_S opcode_STORE rs1 rs2 funct3_SB simm12
  | Sh rs1 rs2 simm12 => encode_S opcode_STORE rs1 rs2 funct3_SH simm12
  | Sw rs1 rs2 simm12 => encode_S opcode_STORE rs1 rs2 funct3_SW simm12
  | Sd rs1 rs2 simm12 => encode_S opcode_STORE rs1 rs2 funct3_SD simm12
  | Add rd rs1 rs2 => encode_R opcode_OP rd rs1 rs2 funct3_ADD funct7_ADD
  | Sub rd rs1 rs2 => None
  | Sll rd rs1 rs2 => None
  | Slt rd rs1 rs2 => None
  | Sltu rd rs1 rs2 => None
  | Xor rd rs1 rs2 => None
  | Srl rd rs1 rs2 => None
  | Sra    rd rs1 rs2 => None
  | Or     rd rs1 rs2 => None
  | And    rd rs1 rs2 => None
  | Mul    rd rs1 rs2 => None
  | Mulh   rd rs1 rs2 => None
  | Mulhsu rd rs1 rs2 => None
  | Mulhu  rd rs1 rs2 => None
  | Div    rd rs1 rs2 => None
  | Divu   rd rs1 rs2 => None
  | Rem    rd rs1 rs2 => None
  | Remu   rd rs1 rs2 => None

  | Lui rd imm20 => None
  | Beq rs1 rs2 sbimm12 => None
  | Bne rs1 rs2 sbimm12 => None
  | Blt rs1 rs2 sbimm12 => None
  | Bge rs1 rs2 sbimm12 => None
  | Bltu rs1 rs2 sbimm12 => None
  | Bgeu rs1 rs2 sbimm12 => None
  | Jalr rd rs1 oimm12 => None
  | Jal rd jimm20 => None

  | Ecall => None
  | Ebreak => None
  | Uret => None
  | Sret => None
  | Mret => None
  | Wfi => None
  | Sfence_vm rs1 rs2 => None

  | Csrrw rd rs1 csr12 => None
  | Csrrs rd rs1 csr12 => None
  | Csrrc rd rs1 csr12 => None
  | Csrrwi rd zimm csr12 => None
  | Csrrsi rd zimm csr12 => None
  | Csrrci rd zimm csr12 => None
  end.



Definition encode_imm12(imm12: Z): option (word 12) :=
  if dec (- 2 ^ 11 <= imm12 < 2 ^ 11) then Some (ZToWord 12 imm12) else None.
