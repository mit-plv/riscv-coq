(*To specify what is leaked by executing a RISC-V instruction, we attempt to follow
  the RISC-V specification of the Zkt extension, as in The RISC-V Instruction Set Manual
  Volume 1, Version 20240411.

  Ideally we'd like to say that if an implementation complies with Zkt, then instructions
  leak no more than what we specify here.  This is not quite true.
  The one exception (so far), branching instructions, will be noted when it comes up.

  In all cases we specify, we assume that in the worst case, an instruction leaks itself and
  all its arguments.  That is, only register contents are leaked--not, for instance, memory
  contents.

  Note that (as can be seen in the definition of leakage_of_instr at the bottom of this file),
  we always leak the full instruction; as the Zkt spec states,
    "Binary executables should not contain secrets in the instruction encodings (Kerckhoffs’s
    principle), so instruction timing may leak information about immediates, ordering of input
    registers, etc."
  Since the map (instruction represented as machine word -> Gallina representation of instruction)
  defined in Decode.v is injective, it suffices to leak the Gallina representation, and this is
  what we do.
*)

Require Import Utility.Utility.

Require Import riscv.Utility.Monads.
Require Import riscv.Utility.MonadNotations.
Require Import riscv.Spec.Decode.

Notation Register := BinInt.Z (only parsing).
Notation "'ReturnSome' x" := (Return (Some x)) (at level 100).

Section WithMonad.
  Context {M : Type -> Type} {MM : Monad M}.

  Inductive LeakageM64 {width} {BW : Bitwidth width} {word: word.word width} : Type :=
  | Mulw_leakage
  | Divw_leakage (num : word) (den : word)
  | Divuw_leakage (num : word) (den : word)
  | Remw_leakage (num : word) (den : word)
  | Remuw_leakage (num : word) (den : word)
  (*| InvalidM64_leakage <- not specified*).
  
  Definition leakage_of_instr_M64 {width} {BW : Bitwidth width} {word: word.word width}
    (getRegister : Register -> M word) (instr : InstructionM64) : M (option LeakageM64) :=
    match instr with
    | Mulw _ _ _ => ReturnSome Mulw_leakage
    | Divw _ rs1 rs2 => num <- getRegister rs1; den <- getRegister rs2; ReturnSome (Divw_leakage num den)
    | Divuw _ rs1 rs2 => num <- getRegister rs1; den <- getRegister rs2; ReturnSome (Divuw_leakage num den)
    | Remw _ rs1 rs2 => num <- getRegister rs1; den <- getRegister rs2; ReturnSome (Remw_leakage num den)
    | Remuw _ rs1 rs2 => num <- getRegister rs1; den <- getRegister rs2; ReturnSome (Remuw_leakage num den)
    | InvalidM64 => Return None
    end.

  Inductive LeakageM {width} {BW : Bitwidth width} {word: word.word width} : Type :=
  | Mul_leakage
  | Mulh_leakage
  | Mulhsu_leakage
  | Mulhu_leakage
  | Div_leakage (num : word) (den : word)
  | Divu_leakage (num : word) (den : word)
  | Rem_leakage (num : word) (den : word)
  | Remu_leakage (num : word) (den : word)
  (*| InvalidM_leakage*).

  Definition leakage_of_instr_M {width} {BW : Bitwidth width} {word: word.word width}
    (getRegister : Register -> M word) (instr : InstructionM) : M (option LeakageM) :=
    match instr with
    | Mul _ _ _ => ReturnSome Mul_leakage
    | Mulh _ _ _ => ReturnSome Mulh_leakage
    | Mulhsu _ _ _ => ReturnSome Mulhsu_leakage
    | Mulhu _ _ _ => ReturnSome Mulhu_leakage
    | Div _ rs1 rs2 => num <- getRegister rs1; den <- getRegister rs2; ReturnSome (Div_leakage num den)
    | Divu _ rs1 rs2 => num <- getRegister rs1; den <- getRegister rs2; ReturnSome (Divu_leakage num den)
    | Rem _ rs1 rs2 => num <- getRegister rs1; den <- getRegister rs2; ReturnSome (Rem_leakage num den)
    | Remu _ rs1 rs2 => num <- getRegister rs1; den <- getRegister rs2; ReturnSome (Remu_leakage num den)
    | InvalidM => Return None
    end.

  Inductive LeakageI64 {width} {BW : Bitwidth width} {word: word.word width} : Type :=
  | Ld_leakage (addr: word)
  | Lwu_leakage (addr: word)
  | Addiw_leakage
  | Slliw_leakage
  | Srliw_leakage
  | Sraiw_leakage
  | Sd_leakage (addr: word)
  | Addw_leakage
  | Subw_leakage
  | Sllw_leakage
  | Srlw_leakage
  | Sraw_leakage
  (*| InvalidI64_leakage*).
  
  Definition leakage_of_instr_I64 {width} {BW : Bitwidth width} {word: word.word width}
    (getRegister : Register -> M word) (instr : InstructionI64) : M (option LeakageI64) :=
    match instr with
    | Ld _ rs1 _ => addr <- getRegister rs1; ReturnSome (Ld_leakage addr)
    | Lwu _ rs1 _ => addr <- getRegister rs1; ReturnSome (Lwu_leakage addr)
    | Addiw _ _ _ => ReturnSome Addiw_leakage
    | Slliw _ _ _ => ReturnSome Slliw_leakage
    | Srliw _ _ _ => ReturnSome Srliw_leakage
    | Sraiw _ _ _ => ReturnSome Sraiw_leakage
    | Sd rs1 _ _ => addr <- getRegister rs1; ReturnSome (Sd_leakage addr)
    | Addw _ _ _ => ReturnSome Addw_leakage
    | Subw _ _ _ => ReturnSome Subw_leakage
    | Sllw _ _ rs2 => ReturnSome Sllw_leakage
    | Srlw _ _ rs2 => ReturnSome Srlw_leakage
    | Sraw _ _ rs2 => ReturnSome Sraw_leakage
    | InvalidI64 => Return None
    end.

  Inductive LeakageI {width} {BW : Bitwidth width} {word: word.word width} : Type :=
  | Lb_leakage (addr: word)
  | Lh_leakage (addr: word)
  | Lw_leakage (addr: word)
  | Lbu_leakage (addr: word)
  | Lhu_leakage (addr: word)
  (*| Fence_leakage <- not implemented*)
  (*| Fence_i_leakage <- not implemented*)
  | Addi_leakage
  | Slli_leakage
  | Slti_leakage
  | Sltiu_leakage
  | Xori_leakage
  | Ori_leakage
  | Andi_leakage
  | Srli_leakage
  | Srai_leakage
  | Auipc_leakage
  | Sb_leakage (addr: word)
  | Sh_leakage (addr: word)
  | Sw_leakage (addr: word)
  | Add_leakage
  | Sub_leakage
  | Sll_leakage
  | Slt_leakage
  | Sltu_leakage
  | Xor_leakage
  | Srl_leakage
  | Sra_leakage
  | Or_leakage
  | And_leakage
  | Lui_leakage
  | Beq_leakage (branch: bool)
  | Bne_leakage (branch: bool)
  | Blt_leakage (branch: bool)
  | Bge_leakage (branch: bool)
  | Bltu_leakage (branch: bool)
  | Bgeu_leakage (branch: bool)
  | Jalr_leakage (addr : word)
  | Jal_leakage
  (*| InvalidI_leakage*).

  (*Here, we assume that branches leak only the value of the branch (i.e., yes or no)
    and not the values being compared, although this is not stated in the spec.*)
  Definition leakage_of_instr_I {width} {BW : Bitwidth width} {word: word.word width}
    (getRegister : Register -> M word) (instr : InstructionI) : M (option LeakageI) :=
    match instr with
    | Lb _ rs1 _ => rs1_val <- getRegister rs1; ReturnSome (Lb_leakage rs1_val)
    | Lh _ rs1 _ => rs1_val <- getRegister rs1; ReturnSome (Lh_leakage rs1_val)
    | Lw _ rs1 _ => rs1_val <- getRegister rs1; ReturnSome (Lw_leakage rs1_val)
    | Lbu _ rs1 _ => rs1_val <- getRegister rs1; ReturnSome(Lbu_leakage rs1_val)
    | Lhu _ rs1 _ => rs1_val <- getRegister rs1; ReturnSome (Lhu_leakage rs1_val)
    | Fence _ _ => Return None
    | Fence_i => Return None
    | Addi _ _ _ => ReturnSome Addi_leakage
    | Slli _ _ _ => ReturnSome Slli_leakage
    | Slti _ _ _ => ReturnSome Slti_leakage
    | Sltiu _ _ _ => ReturnSome Sltiu_leakage
    | Xori _ _ _ => ReturnSome Xori_leakage
    | Ori _ _ _ => ReturnSome Ori_leakage
    | Andi _ _ _ => ReturnSome Andi_leakage
    | Srli _ _ _ => ReturnSome Srli_leakage
    | Srai _ _ _ => ReturnSome Srai_leakage
    | Auipc _ _ => ReturnSome Auipc_leakage
    | Sb rs1 _ _ => rs1_val <- getRegister rs1; ReturnSome (Sb_leakage rs1_val)
    | Sh rs1 _ _ => rs1_val <- getRegister rs1; ReturnSome (Sh_leakage rs1_val)
    | Sw rs1 _ _ => rs1_val <- getRegister rs1; ReturnSome (Sw_leakage rs1_val)
    | Add _ _ _ => ReturnSome Add_leakage
    | Sub _ _ _ => ReturnSome Sub_leakage
    | Sll _ _ rs2 => ReturnSome Sll_leakage
    | Slt _ _ _ => ReturnSome Slt_leakage
    | Sltu _ _ _ => ReturnSome Sltu_leakage
    | Xor _ _ _ => ReturnSome Xor_leakage
    | Srl _ _ rs2 => ReturnSome Srl_leakage
    | Sra _ _ rs2 => ReturnSome Sra_leakage
    | Or _ _ _ => ReturnSome Or_leakage
    | And _ _ _ => ReturnSome And_leakage
    | Lui _ _ => ReturnSome Lui_leakage
    | Beq rs1 rs2 _ => rs1_val <- getRegister rs1; rs2_val <- getRegister rs2; ReturnSome (Beq_leakage (word.eqb rs1_val rs2_val))
    | Bne rs1 rs2 _ => rs1_val <- getRegister rs1; rs2_val <- getRegister rs2; ReturnSome (Bne_leakage (negb (word.eqb rs1_val rs2_val)))
    | Blt rs1 rs2 _ => rs1_val <- getRegister rs1; rs2_val <- getRegister rs2; ReturnSome (Blt_leakage (word.lts rs1_val rs2_val))
    | Bge rs1 rs2 _ => rs1_val <- getRegister rs1; rs2_val <- getRegister rs2; ReturnSome (Bge_leakage (negb (word.lts rs1_val rs2_val)))
    | Bltu rs1 rs2 _ => rs1_val <- getRegister rs1; rs2_val <- getRegister rs2; ReturnSome (Bltu_leakage (word.ltu rs1_val rs2_val))
    | Bgeu rs1 rs2 _ => rs1_val <- getRegister rs1; rs2_val <- getRegister rs2; ReturnSome (Bgeu_leakage (negb (word.ltu rs1_val rs2_val)))
    | Jalr _ rs1 _ => rs1_val <- getRegister rs1; ReturnSome (Jalr_leakage rs1_val)
    | Jal _ _ => ReturnSome Jal_leakage
    | InvalidI => Return None
    end.

  Inductive InstructionLeakage {width} {BW : Bitwidth width} {word: word.word width} : Type :=
  | ILeakage (iLeakage : LeakageI)
  | MLeakage (mLeakage : LeakageM)
  | I64Leakage (i64Leakage : LeakageI64)
  | M64Leakage (m64Leakage : LeakageM64)
  (*| InvalidLeakage*).

  Inductive LeakageEvent {width} {BW : Bitwidth width} {word: word.word width} : Type :=
  | fetchInstr (address : word)
  | executeInstr (instr : Instruction) (ileakage : InstructionLeakage).
  
  Definition instr_leakage {width} {BW : Bitwidth width} {word: word.word width}
    (getRegister : Register -> M word) (instr : Instruction) : M (option InstructionLeakage) :=
    match instr with
    | IInstruction instr => l <- leakage_of_instr_I getRegister instr; Return (option_map ILeakage l)
    | MInstruction instr => l <- leakage_of_instr_M getRegister instr; Return (option_map MLeakage l)
    | AInstruction instr => Return None
    | FInstruction instr => Return None
    | I64Instruction instr => l <- leakage_of_instr_I64 getRegister instr; Return (option_map I64Leakage l)
    | M64Instruction instr => l <- leakage_of_instr_M64 getRegister instr; Return (option_map M64Leakage l)
    | A64Instruction instr => Return None
    | F64Instruction instr => Return None
    | CSRInstruction instr => Return None
    | InvalidInstruction _ => Return None
    end.

  Definition leakage_of_instr {width} {BW : Bitwidth width} {word: word.word width}
    (getRegister : Register -> M word) (instr : Instruction) : M (option LeakageEvent) :=
    l <- instr_leakage getRegister instr; Return (option_map (executeInstr instr) l).

End WithMonad.

Definition concrete_leakage_of_instr {width} {BW: Bitwidth width} {word: word.word width} :=
  @leakage_of_instr (fun T => T) _ width BW word.
