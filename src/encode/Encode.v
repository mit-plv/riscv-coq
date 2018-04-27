(* Need to define Register *)
Require Import Coq.omega.Omega.
Require Import bbv.WordScope.
Require Import bbv.BinNotationZ.
Require Import riscv.RiscvBitWidths.
Require Import riscv.Decode.
Require Import riscv.Utility.


Definition funct3_JALR := Ob"000". (* TODO why does Decode not define & check this? *)

Local Open Scope Z_scope.

Record InstructionMapper{T: Type} := mkInstructionMapper {
  map_Invalid: T;
  map_R(opcode: MachineInt)(rd rs1 rs2: Register)(funct3: MachineInt)(funct7: MachineInt): T;
  map_I(opcode: MachineInt)(rd rs1: Register)(funct3: MachineInt)(oimm12: Z): T;
  map_I_shift_57(opcode: MachineInt)(rd rs1: Register)(shamt5 funct3 funct7: MachineInt): T;
  map_I_shift_66(opcode: MachineInt)(rd rs1: Register)(shamt6 funct3 funct6: MachineInt): T;
  map_I_system(opcode: MachineInt)(rd rs1: Register)(funct3 funct12: MachineInt): T;
  map_S(opcode: MachineInt)(rs1 rs2: Register)(funct3: MachineInt)(simm12: Z): T;
  map_SB(opcode: MachineInt)(rs1 rs2: Register)(funct3: MachineInt)(sbimm12: Z): T;
  map_U(opcode: MachineInt)(rd: Register)(imm20: Z): T;
  map_UJ(opcode: MachineInt)(rd: Register)(jimm20: Z): T;
  map_Fence(opcode: MachineInt)(rd rs1: Register)(funct3: MachineInt)(prd scc msb4: MachineInt): T;
}.

Arguments InstructionMapper: clear implicits.

Definition apply_InstructionMapper{T: Type}(mapper: InstructionMapper T)(inst: Instruction): T :=
  match inst with
  | InvalidInstruction inst   => mapper.(map_Invalid)
  | IInstruction   InvalidI   => mapper.(map_Invalid)
  | MInstruction   InvalidM   => mapper.(map_Invalid)
  | I64Instruction InvalidI64 => mapper.(map_Invalid)
  | M64Instruction InvalidM64 => mapper.(map_Invalid)
  | CSRInstruction InvalidCSR => mapper.(map_Invalid)

  | IInstruction   (Lb  rd rs1 oimm12) => mapper.(map_I) opcode_LOAD rd rs1 funct3_LB  oimm12
  | IInstruction   (Lh  rd rs1 oimm12) => mapper.(map_I) opcode_LOAD rd rs1 funct3_LH  oimm12
  | IInstruction   (Lw  rd rs1 oimm12) => mapper.(map_I) opcode_LOAD rd rs1 funct3_LW  oimm12
  | I64Instruction (Ld  rd rs1 oimm12) => mapper.(map_I) opcode_LOAD rd rs1 funct3_LD  oimm12
  | IInstruction   (Lbu rd rs1 oimm12) => mapper.(map_I) opcode_LOAD rd rs1 funct3_LBU oimm12
  | IInstruction   (Lhu rd rs1 oimm12) => mapper.(map_I) opcode_LOAD rd rs1 funct3_LHU oimm12
  | I64Instruction (Lwu rd rs1 oimm12) => mapper.(map_I) opcode_LOAD rd rs1 funct3_LWU oimm12

  | IInstruction (Fence pred succ) => mapper.(map_Fence) opcode_MISC_MEM 0 0 funct3_FENCE pred succ 0
  | IInstruction (Fence_i) =>         mapper.(map_Fence) opcode_MISC_MEM 0 0 funct3_FENCE_I 0 0 0

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
  end.


Definition encode_Invalid := 0. (* all zeroes is indeed an invalid expression *)

Notation "a <|> b" := (Z.lor a b) (at level 50, left associativity).

Definition encode_R(opcode: MachineInt)(rd rs1 rs2: Register)(funct3 funct7: MachineInt) :=
    opcode <|>
    Z.shiftl rd 7 <|>
    Z.shiftl funct3 12 <|>
    Z.shiftl rs1 15 <|>
    Z.shiftl rs2 20 <|>
    Z.shiftl funct7 25.

Definition encode_I(opcode: MachineInt)(rd rs1: Register)(funct3: MachineInt)(oimm12: Z) :=
    opcode <|>
    Z.shiftl rd 7 <|>
    Z.shiftl funct3 12 <|>
    Z.shiftl rs1 15 <|>
    Z.shiftl oimm12 20.

Definition encode_I_shift_57(opcode: MachineInt)(rd rs1: Register)(shamt5 funct3 funct7: MachineInt) := 
    opcode <|>
    Z.shiftl rd 7 <|>
    Z.shiftl funct3 12 <|>
    Z.shiftl rs1 15 <|>
    Z.shiftl shamt5 20 <|>
    Z.shiftl funct7 25.

Definition encode_I_shift_66(opcode: MachineInt)(rd rs1: Register)(shamt6 funct3 funct6: MachineInt) := 
    opcode <|>
    Z.shiftl rd 7 <|>
    Z.shiftl funct3 12 <|>
    Z.shiftl rs1 15 <|>
    Z.shiftl shamt6 20 <|>
    Z.shiftl funct6 26.

Definition encode_I_system(opcode: MachineInt)(rd rs1: Register)(funct3 funct12: MachineInt) :=
    opcode <|>
    Z.shiftl rd 7 <|>
    Z.shiftl funct3 12 <|>
    Z.shiftl rs1 15 <|>
    Z.shiftl funct12 20.

Definition encode_S(opcode: MachineInt)(rs1 rs2: Register)(funct3: MachineInt)(simm12: Z) :=
    opcode <|>
    Z.shiftl (bitSlice simm12 0 5) 7 <|>
    Z.shiftl funct3 12 <|>
    Z.shiftl rs1 15 <|>
    Z.shiftl rs2 20 <|>
    Z.shiftl (bitSlice simm12 5 12) 25.

Definition encode_SB(opcode: MachineInt)(rs1 rs2: Register)(funct3: MachineInt)(sbimm12: Z) :=
    opcode <|>                                   (*  0..7  (7 bit) *)
    Z.shiftl (bitSlice sbimm12 11 12) 7 <|>         (*  7..8  (1 bit) *)
    Z.shiftl (bitSlice sbimm12 1 5) 8 <|>           (*  8..12 (4 bit) *)
    Z.shiftl funct3 12 <|>                          (* 12..15 (3 bit) *)
    Z.shiftl rs1 15 <|>                             (* 15..20 (5 bit) *)
    Z.shiftl rs2 20 <|>                             (* 20..25 (5 bit) *)
    Z.shiftl (bitSlice sbimm12 5 11) 25 <|>         (* 25..31 (6 bit) *)
    Z.shiftl (bitSlice sbimm12 12 13) 31.           (* 31..32 (1 bit) *)

Definition encode_U(opcode: MachineInt)(rd: Register)(imm20: Z) :=
    opcode <|>
    Z.shiftl rd 7 <|>
    imm20.

Definition encode_UJ(opcode: MachineInt)(rd: Register)(jimm20: Z) :=
    opcode <|>
    Z.shiftl rd 7 <|>
    Z.shiftl (bitSlice jimm20 12 20) 12 <|>
    Z.shiftl (bitSlice jimm20 11 12) 20 <|>
    Z.shiftl (bitSlice jimm20 1 11) 21 <|>
    Z.shiftl (bitSlice jimm20 20 21) 31.

Definition encode_Fence(opcode: MachineInt)(rd rs1: Register)(funct3 prd scc msb4: MachineInt) :=
    opcode <|>                                (*  0..7  (7 bit) *)
    Z.shiftl rd 7 <|>                            (*  7..12 (5 bit) *)
    Z.shiftl funct3 12 <|>                       (* 12..15 (3 bit) *)
    Z.shiftl rs1 15 <|>                          (* 15..20 (5 bit) *)
    Z.shiftl scc 20 <|>                          (* 20..24 (4 bit) *)
    Z.shiftl prd 24 <|>                          (* 24..28 (4 bit) *)
    Z.shiftl msb4 28.                            (* 28..32 (4 bit) *)

Definition Encoder: InstructionMapper MachineInt := {|
  map_Invalid := encode_Invalid;
  map_R := encode_R;
  map_I := encode_I;
  map_I_shift_57 := encode_I_shift_57;
  map_I_shift_66 := encode_I_shift_66;
  map_I_system := encode_I_system;
  map_S := encode_S;
  map_SB := encode_SB;
  map_U := encode_U;
  map_UJ := encode_UJ;
  map_Fence := encode_Fence;
|}.

Definition encode: Instruction -> MachineInt := apply_InstructionMapper Encoder.


Definition verify_Invalid :=
    False.

Definition verify_R(opcode: MachineInt)(rd rs1 rs2: Register)(funct3 funct7: MachineInt) :=
    0 <= opcode < 128 /\
    0 <= rd < 32 /\
    0 <= rs1 < 32 /\
    0 <= rs2 < 32 /\
    0 <= funct3 < 8 /\
    0 <= funct7 < 128.

Definition verify_I(opcode: MachineInt)(rd rs1: Register)(funct3: MachineInt)(oimm12: Z) :=
    0 <= opcode < 128 /\
    0 <= rd < 32 /\
    0 <= rs1 < 32 /\
    0 <= funct3 < 8 /\
    - 2 ^ 11 <= oimm12 < 2 ^ 11.

Definition verify_I_shift_57(opcode: MachineInt)(rd rs1: Register)(shamt5 funct3 funct7: MachineInt) :=
    0 <= opcode < 128 /\
    0 <= rd < 32 /\
    0 <= rs1 < 32 /\
    0 <= shamt5 < 32 /\
    0 <= funct3 < 8 /\
    0 <= funct7 < 128.

Definition verify_I_shift_66(bitwidth: Z)(opcode: MachineInt)(rd rs1: Register)(shamt6 funct3 funct6: MachineInt) :=
    0 <= opcode < 128 /\
    0 <= rd < 32 /\
    0 <= rs1 < 32 /\
    0 <= shamt6 < bitwidth /\
    0 <= funct3 < 8 /\
    0 <= funct6 < 64.

Definition verify_I_system(opcode: MachineInt)(rd rs1: Register)(funct3 funct12: MachineInt) :=
    0 <= opcode < 128 /\
    0 <= rd < 32 /\
    0 <= rs1 < 32 /\
    0 <= funct3 < 8 /\
    0 <= funct12 < 4096.

Definition verify_S(opcode: MachineInt)(rs1 rs2: Register)(funct3: MachineInt)(simm12: Z) :=
    0 <= opcode < 128 /\
    0 <= rs1 < 32 /\
    0 <= rs2 < 32 /\
    0 <= funct3 < 8 /\
    - 2 ^ 11 <= simm12 < 2 ^ 11.

Definition verify_SB(opcode: MachineInt)(rs1 rs2: Register)(funct3: MachineInt)(sbimm12: Z) :=
    0 <= opcode < 128 /\
    0 <= rs1 < 32 /\
    0 <= rs2 < 32 /\
    0 <= funct3 < 8 /\
    - 2 ^ 12 <= sbimm12 < 2 ^ 12 /\ sbimm12 mod 2 = 0.

Definition verify_U(opcode: MachineInt)(rd: Register)(imm20: Z) :=
    0 <= opcode < 128 /\
    0 <= rd < 32 /\
    - 2 ^ 31 <= imm20 < 2 ^ 31 /\ imm20 mod 2 ^ 12 = 0.

Definition verify_UJ(opcode: MachineInt)(rd: Register)(jimm20: Z) :=
    0 <= opcode < 128 /\
    0 <= rd < 32 /\
    - 2 ^ 20 <= jimm20 < 2 ^ 20 /\ jimm20 mod 2 = 0.

Definition verify_Fence(opcode: MachineInt)(rd rs1: Register)(funct3 prd scc msb4: MachineInt) :=
    0 <= opcode < 128 /\
    0 <= rd < 32 /\
    0 <= rs1 < 32 /\
    0 <= funct3 < 8 /\
    0 <= prd < 16 /\
    0 <= scc < 16 /\
    0 <= msb4 < 16.

(* Only verifies that each field is within bounds and has the correct modulus.
   Validity of opcodes and funct codes follows from the fact that it was an Instruction. *)
Definition Verifier(bitwidth: Z): InstructionMapper Prop := {|
  map_Invalid := verify_Invalid;
  map_R := verify_R;
  map_I := verify_I;
  map_I_shift_57 := verify_I_shift_57;
  map_I_shift_66 := verify_I_shift_66 bitwidth;
  map_I_system := verify_I_system;
  map_S := verify_S;
  map_SB := verify_SB;
  map_U := verify_U;
  map_UJ := verify_UJ;
  map_Fence := verify_Fence;
|}.

Definition respects_bounds(bitwidth: Z): Instruction -> Prop :=
  apply_InstructionMapper (Verifier bitwidth).

Hint Unfold
  map_Invalid
  map_R
  map_I
  map_I_shift_57
  map_I_shift_66
  map_I_system
  map_S
  map_SB
  map_U
  map_UJ
  map_Fence
  Verifier
  Encoder
  apply_InstructionMapper
: mappers.

Goal (respects_bounds 32 (IInstruction (Jal 0 3))).
  simpl. unfold verify_UJ.
  (* wrong, as expected *)
Abort.

Goal (respects_bounds 32 (IInstruction (Jal 0 4))).
  simpl. unfold verify_UJ.
  unfold opcode_JAL.
  cbn.
  omega.
Qed.

Require Import bbv.HexNotationZ.

(* This expression will generate a runtime exception, because the jump target is not
   a multiple of 4 *)
Example invalid_Jal_encode_example: encode (IInstruction (Jal 0 3)) = Ox"20006F". reflexivity. Qed.

(* Note: The least significant bit of the jump target is not encoded, because even
   in compressed instructions, jump targets are always a multiple of 2. *)
Example Jal_encode_loses_lsb: decode RV64IM (Ox"20006F") = IInstruction (Jal 0 2). reflexivity. Qed.

