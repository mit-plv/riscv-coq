Require Import Coq.omega.Omega.
Require Import riscv.util.Decidable.
Require Import riscv.util.NameWithEq.
Require Import riscv.RiscvBitWidths.
Require Import riscv.Utility.
Require Import bbv.BinNotationZ.
Require Import bbv.HexNotationZ.

Local Open Scope Z_scope.

Notation "a <|> b" := (Z.lor a b) (at level 50, left associativity).

Section Instructions.

Context {Name: NameWithEq}. (* register name *)
Notation Register := (@name Name).

Definition Imm := Z.

Inductive Instruction : Set :=
(* begin instructions *)
  | InvalidInstruction

  | Lb(rd: Register)(rs1: Register)(oimm12: MachineInt)
  | Lh(rd: Register)(rs1: Register)(oimm12: MachineInt)
  | Lw(rd: Register)(rs1: Register)(oimm12: MachineInt)
  | Ld(rd: Register)(rs1: Register)(oimm12: MachineInt)
  | Lbu(rd: Register)(rs1: Register)(oimm12: MachineInt)
  | Lhu(rd: Register)(rs1: Register)(oimm12: MachineInt)
  | Lwu(rd: Register)(rs1: Register)(oimm12: MachineInt)

  | Fence(pred: MachineInt)(succ: MachineInt)
  | Fence_i

  | Addi(rd: Register)(rs1: Register)(imm12: MachineInt)
  | Slli(rd: Register)(rs1: Register)(shamt6: MachineInt)
  | Slti(rd: Register)(rs1: Register)(imm12: MachineInt)
  | Sltiu(rd: Register)(rs1: Register)(imm12: MachineInt)
  | Xori(rd: Register)(rs1: Register)(imm12: MachineInt)
  | Ori(rd: Register)(rs1: Register)(imm12: MachineInt)
  | Andi(rd: Register)(rs1: Register)(imm12: MachineInt)
  | Srli(rd: Register)(rs1: Register)(shamt6: MachineInt)
  | Srai(rd: Register)(rs1: Register)(shamt6: MachineInt)

  | Auipc(rd: Register)(oimm20: MachineInt)

  | Addiw(rd: Register)(rs1: Register)(imm12: MachineInt)
  | Slliw(rd: Register)(rs1: Register)(shamt5: MachineInt)
  | Srliw(rd: Register)(rs1: Register)(shamt5: MachineInt)
  | Sraiw(rd: Register)(rs1: Register)(shamt5: MachineInt)

  | Sb(rs1: Register)(rs2: Register)(simm12: MachineInt)
  | Sh(rs1: Register)(rs2: Register)(simm12: MachineInt)
  | Sw(rs1: Register)(rs2: Register)(simm12: MachineInt)
  | Sd(rs1: Register)(rs2: Register)(simm12: MachineInt)

  | Add(rd: Register)(rs1: Register)(rs2: Register)
  | Sub(rd: Register)(rs1: Register)(rs2: Register)
  | Sll(rd: Register)(rs1: Register)(rs2: Register)
  | Slt(rd: Register)(rs1: Register)(rs2: Register)
  | Sltu(rd: Register)(rs1: Register)(rs2: Register)
  | Xor(rd: Register)(rs1: Register)(rs2: Register)
  | Srl(rd: Register)(rs1: Register)(rs2: Register)
  | Sra(rd: Register)(rs1: Register)(rs2: Register)
  | Or(rd: Register)(rs1: Register)(rs2: Register)
  | And(rd: Register)(rs1: Register)(rs2: Register)
  | Mul(rd: Register)(rs1: Register)(rs2: Register)
  | Mulh(rd: Register)(rs1: Register)(rs2: Register)
  | Mulhsu(rd: Register)(rs1: Register)(rs2: Register)
  | Mulhu(rd: Register)(rs1: Register)(rs2: Register)
  | Div(rd: Register)(rs1: Register)(rs2: Register)
  | Divu(rd: Register)(rs1: Register)(rs2: Register)
  | Rem(rd: Register)(rs1: Register)(rs2: Register)
  | Remu(rd: Register)(rs1: Register)(rs2: Register)

  | Lui(rd: Register)(imm20: MachineInt)

  | Addw(rd: Register)(rs1: Register)(rs2: Register)
  | Subw(rd: Register)(rs1: Register)(rs2: Register)
  | Sllw(rd: Register)(rs1: Register)(rs2: Register)
  | Srlw(rd: Register)(rs1: Register)(rs2: Register)
  | Sraw(rd: Register)(rs1: Register)(rs2: Register)
  | Mulw(rd: Register)(rs1: Register)(rs2: Register)
  | Divw(rd: Register)(rs1: Register)(rs2: Register)
  | Divuw(rd: Register)(rs1: Register)(rs2: Register)
  | Remw(rd: Register)(rs1: Register)(rs2: Register)
  | Remuw(rd: Register)(rs1: Register)(rs2: Register)

  | Beq(rs1: Register)(rs2: Register)(sbimm12: MachineInt)
  | Bne(rs1: Register)(rs2: Register)(sbimm12: MachineInt)
  | Blt(rs1: Register)(rs2: Register)(sbimm12: MachineInt)
  | Bge(rs1: Register)(rs2: Register)(sbimm12: MachineInt)
  | Bltu(rs1: Register)(rs2: Register)(sbimm12: MachineInt)
  | Bgeu(rs1: Register)(rs2: Register)(sbimm12: MachineInt)

  | Jalr(rd: Register)(rs1: Register)(oimm12: MachineInt)

  | Jal(rd: Register)(jimm20: MachineInt)

  | Ecall
  | Ebreak
  | Uret
  | Sret
  | Mret
  | Wfi
  | Sfence_vm(rs1: Register)(rs2: Register)

  | Csrrw(rd: Register)(rs1: Register)(csr12: MachineInt)
  | Csrrs(rd: Register)(rs1: Register)(csr12: MachineInt)
  | Csrrc(rd: Register)(rs1: Register)(csr12: MachineInt)
  | Csrrwi(rd: Register)(zimm: MachineInt)(csr12: MachineInt)
  | Csrrsi(rd: Register)(zimm: MachineInt)(csr12: MachineInt)
  | Csrrci(rd: Register)(zimm: MachineInt)(csr12: MachineInt)
(* end instructions *)
.

End Instructions.

(* Note: we could also use this notation:
Eval cbv in (1~0~1~0)%positive.
But it doesn't allow leading zeros, nor zero values. *)

(* begin constants *)

Definition opcode_LOAD       := Ob"0000011".
Definition opcode_LOAD_FP    := Ob"0000111".
Definition opcode_MISC_MEM   := Ob"0001111".
Definition opcode_OP_IMM     := Ob"0010011".
Definition opcode_AUIPC      := Ob"0010111".
Definition opcode_OP_IMM_32  := Ob"0011011".

Definition opcode_STORE      := Ob"0100011".
Definition opcode_STORE_FP   := Ob"0100111".
Definition opcode_AMO        := Ob"0101111".
Definition opcode_OP         := Ob"0110011".
Definition opcode_LUI        := Ob"0110111".
Definition opcode_OP_32      := Ob"0111011".

Definition opcode_MADD       := Ob"1000011".
Definition opcode_MSUB       := Ob"1000111".
Definition opcode_NMSUB      := Ob"1001011".
Definition opcode_NMADD      := Ob"1001111".
Definition opcode_OP_FP      := Ob"1010011".

Definition opcode_BRANCH     := Ob"1100011".
Definition opcode_JALR       := Ob"1100111".
Definition opcode_JAL        := Ob"1101111".
Definition opcode_SYSTEM     := Ob"1110011".

(* LOAD sub-opcodes *)
Definition funct3_LB   := Ob"000".
Definition funct3_LH   := Ob"001".
Definition funct3_LW   := Ob"010".
Definition funct3_LD   := Ob"011".
Definition funct3_LBU  := Ob"100".
Definition funct3_LHU  := Ob"101".
Definition funct3_LWU  := Ob"110".

(* MISC_MEM sub-opcodes *)
Definition funct3_FENCE    := Ob"000".
Definition funct3_FENCE_I  := Ob"001".

(* OP_IMM sub-opcodes *)
Definition funct3_ADDI   := Ob"000".
Definition funct3_SLLI   := Ob"001".
Definition funct3_SLTI   := Ob"010".
Definition funct3_SLTIU  := Ob"011".
Definition funct3_XORI   := Ob"100".
Definition funct3_SRLI   := Ob"101".
Definition funct3_SRAI   := Ob"101".
Definition funct3_ORI    := Ob"110".
Definition funct3_ANDI   := Ob"111".

(* OP_IMM.SLLI/SRLI/SRAI for RV32 *)
Definition funct7_SLLI   := Ob"0000000".
Definition funct7_SRLI   := Ob"0000000".
Definition funct7_SRAI   := Ob"0100000".
(* OP_IMM.SLLI/SRLI/SRAI for RV64 *)
Definition funct6_SLLI   := Ob"000000".
Definition funct6_SRLI   := Ob"000000".
Definition funct6_SRAI   := Ob"010000".

(* OP_IMM_32 sub-opcodes (RV64 only) *)
Definition funct3_ADDIW  := Ob"000".

Definition funct3_SLLIW  := Ob"001".
Definition funct7_SLLIW  := Ob"0000000".

Definition funct3_SRLIW  := Ob"101".
Definition funct7_SRLIW  := Ob"0000000".

Definition funct3_SRAIW  := Ob"101".
Definition funct7_SRAIW  := Ob"0100000".

(* STORE sub-opcodes *)
Definition funct3_SB  := Ob"000".
Definition funct3_SH  := Ob"001".
Definition funct3_SW  := Ob"010".
Definition funct3_SD  := Ob"011".

(* OP sub-opcodes *)
Definition funct3_ADD   := Ob"000".
Definition funct7_ADD   := Ob"0000000".

Definition funct3_SUB   := Ob"000".
Definition funct7_SUB   := Ob"0100000".

Definition funct3_SLL   := Ob"001".
Definition funct7_SLL   := Ob"0000000".

Definition funct3_SLT   := Ob"010".
Definition funct7_SLT   := Ob"0000000".

Definition funct3_SLTU  := Ob"011".
Definition funct7_SLTU  := Ob"0000000".

Definition funct3_XOR   := Ob"100".
Definition funct7_XOR   := Ob"0000000".

Definition funct3_SRL   := Ob"101".
Definition funct7_SRL   := Ob"0000000".

Definition funct3_SRA   := Ob"101".
Definition funct7_SRA   := Ob"0100000".

Definition funct3_OR    := Ob"110".
Definition funct7_OR    := Ob"0000000".

Definition funct3_AND   := Ob"111".
Definition funct7_AND   := Ob"0000000".

(* OP sub-opcodes, M standard extension *)

Definition funct3_MUL     := Ob"000".
Definition funct7_MUL     := Ob"0000001".

Definition funct3_MULH    := Ob"001".
Definition funct7_MULH    := Ob"0000001".

Definition funct3_MULHSU  := Ob"010".
Definition funct7_MULHSU  := Ob"0000001".

Definition funct3_MULHU   := Ob"011".
Definition funct7_MULHU   := Ob"0000001".

Definition funct3_DIV     := Ob"100".
Definition funct7_DIV     := Ob"0000001".

Definition funct3_DIVU    := Ob"101".
Definition funct7_DIVU    := Ob"0000001".

Definition funct3_REM     := Ob"110".
Definition funct7_REM     := Ob"0000001".

Definition funct3_REMU    := Ob"111".
Definition funct7_REMU    := Ob"0000001".

(* OP_32 sub-opcodes (RV64 only) *)
Definition funct3_ADDW   := Ob"000".
Definition funct7_ADDW   := Ob"0000000".

Definition funct3_SUBW   := Ob"000".
Definition funct7_SUBW   := Ob"0100000".

Definition funct3_SLLW   := Ob"001".
Definition funct7_SLLW   := Ob"0000000".

Definition funct3_SRLW   := Ob"101".
Definition funct7_SRLW   := Ob"0000000".

Definition funct3_SRAW   := Ob"101".
Definition funct7_SRAW   := Ob"0100000".

(* OP_32 sub-opcodes, M standard extension (RV64 only) *)
Definition funct3_MULW   := Ob"000".
Definition funct7_MULW   := Ob"0000001".

Definition funct3_DIVW   := Ob"100".
Definition funct7_DIVW   := Ob"0000001".

Definition funct3_DIVUW  := Ob"101".
Definition funct7_DIVUW  := Ob"0000001".

Definition funct3_REMW   := Ob"110".
Definition funct7_REMW   := Ob"0000001".

Definition funct3_REMUW  := Ob"111".
Definition funct7_REMUW  := Ob"0000001".

(* BRANCH sub-opcodes *)
Definition funct3_BEQ   := Ob"000".
Definition funct3_BNE   := Ob"001".
Definition funct3_BLT   := Ob"100".
Definition funct3_BGE   := Ob"101".
Definition funct3_BLTU  := Ob"110".
Definition funct3_BGEU  := Ob"111".

(* SYSTEM sub-opcodes *)
Definition funct3_PRIV    := Ob"000".
(*- SYSTEM.PRIV sub-sub-opcodes *)
Definition funct12_ECALL     := Ob"000000000000".
Definition funct12_EBREAK    := Ob"000000000001".
Definition funct12_URET      := Ob"000000000010".
Definition funct12_SRET      := Ob"000100000010".
Definition funct12_MRET      := Ob"001100000010".
Definition funct12_WFI       := Ob"000100000101".

Definition funct7_SFENCE_VM  := Ob"0001001".

Definition funct3_CSRRW   := Ob"001".
Definition funct3_CSRRS   := Ob"010".
Definition funct3_CSRRC   := Ob"011".
Definition funct3_CSRRWI  := Ob"101".
Definition funct3_CSRRSI  := Ob"110".
Definition funct3_CSRRCI  := Ob"111".

(* TODO: sub-opcodes for LOAD_FP, STORE_FP, OP_FP *)
(* TODO: sub-opcodes for AMO *)
(* TODO: sub-opcodes for MADD, MSUB, NMSUB, NMADD *)

(* end constants *)

Definition shift := Z.shiftl.

Local Instance ZName: NameWithEq := {|
  name := Z
|}.

Local Open Scope bool_scope.

Definition decode (xlen inst : MachineInt) : Instruction :=
(* begin decode *)
    let opcode  := bitSlice inst 0 7 in
    let funct3  := bitSlice inst 12 15 in
    let funct7  := bitSlice inst 25 32 in
    let funct10 := (shift (bitSlice inst 25 32) 3) <|> (bitSlice inst 12 15) in
    let funct12 := bitSlice inst 20 32 in

    let rd      := bitSlice inst 7 12 in
    let rs1     := bitSlice inst 15 20 in
    let rs2     := bitSlice inst 20 25 in
    let rs3     := bitSlice inst 27 32 in

    let succ    := bitSlice inst 20 24 in
    let pred    := bitSlice inst 24 28 in
    let msb4    := bitSlice inst 28 32 in

    let imm20   := signExtend 32 (shift (bitSlice inst 12 32) 12) in
    let oimm20  := signExtend 32 (shift (bitSlice inst 12 32) 12) in

    let jimm20  := signExtend 21 ((shift (bitSlice inst 31 32) 20  <|>
                                shift (bitSlice inst 21 31) 1  <|>
                                shift (bitSlice inst 20 21) 11 <|>
                                shift (bitSlice inst 12 20) 12)) in

    let imm12   := signExtend 12 (bitSlice inst 20 32) in
    let oimm12  := signExtend 12 (bitSlice inst 20 32) in

    let csr12   := bitSlice inst 20 32 in

    let simm12  := signExtend 12 (shift (bitSlice inst 25 32) 5 <|> bitSlice inst 7 12) in

    let sbimm12 := signExtend 13 ((shift (bitSlice inst 31 32) 12 <|>
                                shift (bitSlice inst 25 31) 5 <|>
                                shift (bitSlice inst 8 12) 1  <|>
                                shift (bitSlice inst 7 8) 11)) in

    let shamt5  := bitSlice inst 20 25 in
    let shamt6  := bitSlice inst 20 26 in
    let funct6  := bitSlice inst 26 32 in

    let zimm    := bitSlice inst 15 20 in

    if (opcode =? opcode_LOAD) && (funct3 =? funct3_LB) then Lb rd rs1 oimm12 else
    if (opcode =? opcode_LOAD) && (funct3 =? funct3_LH) then Lh rd rs1 oimm12 else
    if (opcode =? opcode_LOAD) && (funct3 =? funct3_LW) then Lw rd rs1 oimm12 else
    if (opcode =? opcode_LOAD) && (funct3 =? funct3_LBU) then Lbu rd rs1 oimm12 else
    if (opcode =? opcode_LOAD) && (funct3 =? funct3_LHU) then Lhu rd rs1 oimm12 else

    if (opcode =? opcode_MISC_MEM) && (rd =? 0) && (funct3 =? funct3_FENCE) && (rs1 =? 0) && (msb4 =? 0) then Fence pred succ else
    if (opcode =? opcode_MISC_MEM) && (rd =? 0) && (funct3 =? funct3_FENCE_I) && (rs1 =? 0) && (imm12 =? 0) then Fence_i  else

    if (opcode =? opcode_OP_IMM) && (funct3 =? funct3_ADDI) then Addi rd rs1 imm12 else
    if (opcode =? opcode_OP_IMM) && (funct3 =? funct3_SLLI) && (funct7 =? funct7_SLLI) && (xlen =? 32) then Slli rd rs1 shamt5 else
    if (opcode =? opcode_OP_IMM) && (funct3 =? funct3_SLTI) then Slti rd rs1 imm12 else
    if (opcode =? opcode_OP_IMM) && (funct3 =? funct3_SLTIU) then Sltiu rd rs1 imm12 else
    if (opcode =? opcode_OP_IMM) && (funct3 =? funct3_XORI) then Xori rd rs1 imm12 else
    if (opcode =? opcode_OP_IMM) && (funct3 =? funct3_ORI) then Ori rd rs1 imm12 else
    if (opcode =? opcode_OP_IMM) && (funct3 =? funct3_ANDI) then Andi rd rs1 imm12 else
    if (opcode =? opcode_OP_IMM) && (funct3 =? funct3_SRLI) && (funct7 =? funct7_SRLI) && (xlen =? 32) then Srli rd rs1 shamt5 else
    if (opcode =? opcode_OP_IMM) && (funct3 =? funct3_SRAI) && (funct7 =? funct7_SRAI) && (xlen =? 32) then Srai rd rs1 shamt5 else

    if (opcode =? opcode_AUIPC) then Auipc rd oimm20 else

    if (opcode =? opcode_STORE) && (funct3 =? funct3_SB) then Sb rs1 rs2 simm12 else
    if (opcode =? opcode_STORE) && (funct3 =? funct3_SH) then Sh rs1 rs2 simm12 else
    if (opcode =? opcode_STORE) && (funct3 =? funct3_SW) then Sw rs1 rs2 simm12 else

    if (opcode =? opcode_OP) && (funct3 =? funct3_ADD) && (funct7 =? funct7_ADD) then Add rd rs1 rs2 else
    if (opcode =? opcode_OP) && (funct3 =? funct3_SUB) && (funct7 =? funct7_SUB) then Sub rd rs1 rs2 else
    if (opcode =? opcode_OP) && (funct3 =? funct3_SLL) && (funct7 =? funct7_SLL) then Sll rd rs1 rs2 else
    if (opcode =? opcode_OP) && (funct3 =? funct3_SLT) && (funct7 =? funct7_SLT) then Slt rd rs1 rs2 else
    if (opcode =? opcode_OP) && (funct3 =? funct3_SLTU) && (funct7 =? funct7_SLTU) then Sltu rd rs1 rs2 else
    if (opcode =? opcode_OP) && (funct3 =? funct3_XOR) && (funct7 =? funct7_XOR) then Xor rd rs1 rs2 else
    if (opcode =? opcode_OP) && (funct3 =? funct3_SRL) && (funct7 =? funct7_SRL) then Srl rd rs1 rs2 else
    if (opcode =? opcode_OP) && (funct3 =? funct3_SRA) && (funct7 =? funct7_SRA) then Sra rd rs1 rs2 else
    if (opcode =? opcode_OP) && (funct3 =? funct3_OR) && (funct7 =? funct7_OR) then Or rd rs1 rs2 else
    if (opcode =? opcode_OP) && (funct3 =? funct3_AND) && (funct7 =? funct7_AND) then And rd rs1 rs2 else

    if (opcode =? opcode_OP) && (funct3 =? funct3_MUL) && (funct7 =? funct7_MUL) then Mul rd rs1 rs2 else
    if (opcode =? opcode_OP) && (funct3 =? funct3_MULH) && (funct7 =? funct7_MULH) then Mulh rd rs1 rs2 else
    if (opcode =? opcode_OP) && (funct3 =? funct3_MULHSU) && (funct7 =? funct7_MULHSU) then Mulhsu rd rs1 rs2 else
    if (opcode =? opcode_OP) && (funct3 =? funct3_MULHU) && (funct7 =? funct7_MULHU) then Mulhu rd rs1 rs2 else
    if (opcode =? opcode_OP) && (funct3 =? funct3_DIV) && (funct7 =? funct7_DIV) then Div rd rs1 rs2 else
    if (opcode =? opcode_OP) && (funct3 =? funct3_DIVU) && (funct7 =? funct7_DIVU) then Divu rd rs1 rs2 else
    if (opcode =? opcode_OP) && (funct3 =? funct3_REM) && (funct7 =? funct7_REM) then Rem rd rs1 rs2 else
    if (opcode =? opcode_OP) && (funct3 =? funct3_REMU) && (funct7 =? funct7_REMU) then Remu rd rs1 rs2 else

    if (opcode =? opcode_LUI) then Lui rd imm20 else

    if (opcode =? opcode_BRANCH) && (funct3 =? funct3_BEQ) then Beq rs1 rs2 sbimm12 else
    if (opcode =? opcode_BRANCH) && (funct3 =? funct3_BNE) then Bne rs1 rs2 sbimm12 else
    if (opcode =? opcode_BRANCH) && (funct3 =? funct3_BLT) then Blt rs1 rs2 sbimm12 else
    if (opcode =? opcode_BRANCH) && (funct3 =? funct3_BGE) then Bge rs1 rs2 sbimm12 else
    if (opcode =? opcode_BRANCH) && (funct3 =? funct3_BLTU) then Bltu rs1 rs2 sbimm12 else
    if (opcode =? opcode_BRANCH) && (funct3 =? funct3_BGEU) then Bgeu rs1 rs2 sbimm12 else

    if (opcode =? opcode_JALR) then Jalr rd rs1 oimm12 else

    if (opcode =? opcode_JAL) then Jal rd jimm20 else

    if (opcode =? opcode_SYSTEM) && (rd =? 0) && (funct3 =? funct3_PRIV) && (rs1 =? 0) && (funct12 =? funct12_ECALL) then Ecall  else
    if (opcode =? opcode_SYSTEM) && (rd =? 0) && (funct3 =? funct3_PRIV) && (rs1 =? 0) && (funct12 =? funct12_EBREAK) then Ebreak  else
    if (opcode =? opcode_SYSTEM) && (rd =? 0) && (funct3 =? funct3_PRIV) && (rs1 =? 0) && (funct12 =? funct12_URET) then Uret  else
    if (opcode =? opcode_SYSTEM) && (rd =? 0) && (funct3 =? funct3_PRIV) && (rs1 =? 0) && (funct12 =? funct12_SRET) then Sret  else
    if (opcode =? opcode_SYSTEM) && (rd =? 0) && (funct3 =? funct3_PRIV) && (rs1 =? 0) && (funct12 =? funct12_MRET) then Mret  else
    if (opcode =? opcode_SYSTEM) && (rd =? 0) && (funct3 =? funct3_PRIV) && (rs1 =? 0) && (funct12 =? funct12_WFI) then Wfi  else

    if (opcode =? opcode_SYSTEM) && (rd =? 0) && (funct3 =? funct3_PRIV) && (funct7 =? funct7_SFENCE_VM) then Sfence_vm rs1 rs2 else

    if (opcode =? opcode_SYSTEM) && (funct3 =? funct3_CSRRW) then Csrrw rd rs1   csr12 else
    if (opcode =? opcode_SYSTEM) && (funct3 =? funct3_CSRRS) then Csrrw rd rs1   csr12 else
    if (opcode =? opcode_SYSTEM) && (funct3 =? funct3_CSRRC) then Csrrw rd rs1   csr12 else
    if (opcode =? opcode_SYSTEM) && (funct3 =? funct3_CSRRWI) then Csrrwi rd zimm csr12 else
    if (opcode =? opcode_SYSTEM) && (funct3 =? funct3_CSRRSI) then Csrrwi rd zimm csr12 else
    if (opcode =? opcode_SYSTEM) && (funct3 =? funct3_CSRRCI) then Csrrwi rd zimm csr12 else

    if (opcode =? opcode_LOAD) && (funct3 =? funct3_LD) && (xlen =? 64) then Ld rd rs1 oimm12 else
    if (opcode =? opcode_LOAD) && (funct3 =? funct3_LWU) && (xlen =? 64) then Lwu rd rs1 oimm12 else

    if (opcode =? opcode_OP_IMM) && (funct3 =? funct3_SLLI) && (funct6 =? funct6_SLLI) && (xlen =? 64) then Slli rd rs1 shamt6 else
    if (opcode =? opcode_OP_IMM) && (funct3 =? funct3_SRLI) && (funct6 =? funct6_SRLI) && (xlen =? 64) then Srli rd rs1 shamt6 else
    if (opcode =? opcode_OP_IMM) && (funct3 =? funct3_SRAI) && (funct6 =? funct6_SRAI) && (xlen =? 64) then Srai rd rs1 shamt6 else

    if (opcode =? opcode_OP_IMM_32) && (funct3 =? funct3_ADDIW) && (xlen =? 64) then Addiw rd rs1 imm12 else
    if (opcode =? opcode_OP_IMM_32) && (funct3 =? funct3_SLLIW) && (funct7 =? funct7_SLLIW) && (xlen =? 64) then Slliw rd rs1 shamt5 else
    if (opcode =? opcode_OP_IMM_32) && (funct3 =? funct3_SRLIW) && (funct7 =? funct7_SRLIW) && (xlen =? 64) then Srliw rd rs1 shamt5 else
    if (opcode =? opcode_OP_IMM_32) && (funct3 =? funct3_SRAIW) && (funct7 =? funct7_SRAIW) && (xlen =? 64) then Sraiw rd rs1 shamt5 else

    if (opcode =? opcode_STORE) && (funct3 =? funct3_SD) && (xlen =? 64) then Sd rs1 rs2 simm12 else

    if (opcode =? opcode_OP_32) && (funct3 =? funct3_ADDW) && (funct7 =? funct7_ADDW) && (xlen =? 64) then Addw rd rs1 rs2 else
    if (opcode =? opcode_OP_32) && (funct3 =? funct3_SUBW) && (funct7 =? funct7_SUBW) && (xlen =? 64) then Subw rd rs1 rs2 else
    if (opcode =? opcode_OP_32) && (funct3 =? funct3_SLLW) && (funct7 =? funct7_SLLW) && (xlen =? 64) then Sllw rd rs1 rs2 else
    if (opcode =? opcode_OP_32) && (funct3 =? funct3_SRLW) && (funct7 =? funct7_SRLW) && (xlen =? 64) then Srlw rd rs1 rs2 else
    if (opcode =? opcode_OP_32) && (funct3 =? funct3_SRAW) && (funct7 =? funct7_SRAW) && (xlen =? 64) then Sraw rd rs1 rs2 else

    if (opcode =? opcode_OP_32) && (funct3 =? funct3_MULW) && (funct7 =? funct7_MULW) && (xlen =? 64) then Mulw rd rs1 rs2 else
    if (opcode =? opcode_OP_32) && (funct3 =? funct3_DIVW) && (funct7 =? funct7_DIVW) && (xlen =? 64) then Divw rd rs1 rs2 else
    if (opcode =? opcode_OP_32) && (funct3 =? funct3_DIVUW) && (funct7 =? funct7_DIVUW) && (xlen =? 64) then Divuw rd rs1 rs2 else
    if (opcode =? opcode_OP_32) && (funct3 =? funct3_REMW) && (funct7 =? funct7_REMW) && (xlen =? 64) then Remw rd rs1 rs2 else
    if (opcode =? opcode_OP_32) && (funct3 =? funct3_REMUW) && (funct7 =? funct7_REMUW) && (xlen =? 64) then Remuw rd rs1 rs2 else

(* end decode *)
    InvalidInstruction.


Definition test_instruction: Z :=   Ox"0140006f".

Definition test_result: Instruction := decode 32 test_instruction.

Goal test_result = Jal 0 20.
  reflexivity.
Qed.
