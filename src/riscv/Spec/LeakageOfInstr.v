Require Import Utility.Utility.

Require Import riscv.Utility.Monads.
Require Import riscv.Utility.MonadNotations.
Require Import riscv.Spec.Decode.

Notation Register := BinInt.Z (only parsing).

Section WithMonad.
  Context {M : Type -> Type} {MM : Monad M}.
  
  Inductive LeakageM64 {width} {BW : Bitwidth width} {word: word.word width} : Type :=
  | Mulw_leakage
  | Divw_leakage (num : word) (den : word)
  | Divuw_leakage (num : word) (den : word)
  | Remw_leakage (num : word) (den : word)
  | Remuw_leakage (num : word) (den : word)
  | InvalidM64_leakage.
  
  Definition leakage_of_instr_M64 {width} {BW : Bitwidth width} {word: word.word width}
    (getRegister : Register -> M word) (instr : InstructionM64) : M LeakageM64 :=
    match instr with
    | Mulw _ _ _ => Return Mulw_leakage
    | Divw _ rs1 rs2 => num <- getRegister rs1; den <- getRegister rs2; Return (Divw_leakage num den)
    | Divuw _ rs1 rs2 => num <- getRegister rs1; den <- getRegister rs2; Return (Divuw_leakage num den)
    | Remw _ rs1 rs2 => num <- getRegister rs1; den <- getRegister rs2; Return (Remw_leakage num den)
    | Remuw _ rs1 rs2 => num <- getRegister rs1; den <- getRegister rs2; Return (Remuw_leakage num den)
    | InvalidM64 => Return InvalidM64_leakage
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
  | InvalidM_leakage.

  Definition leakage_of_instr_M {width} {BW : Bitwidth width} {word: word.word width}
    (getRegister : Register -> M word) (instr : InstructionM) : M LeakageM :=
    match instr with
    | Mul _ _ _ => Return Mul_leakage
    | Mulh _ _ _ => Return Mulh_leakage
    | Mulhsu _ _ _ => Return Mulhsu_leakage
    | Mulhu _ _ _ => Return Mulhu_leakage
    | Div _ rs1 rs2 => num <- getRegister rs1; den <- getRegister rs2; Return (Div_leakage num den)
    | Divu _ rs1 rs2 => num <- getRegister rs1; den <- getRegister rs2; Return (Divu_leakage num den)
    | Rem _ rs1 rs2 => num <- getRegister rs1; den <- getRegister rs2; Return (Rem_leakage num den)
    | Remu _ rs1 rs2 => num <- getRegister rs1; den <- getRegister rs2; Return (Remu_leakage num den)
    | InvalidM => Return InvalidM_leakage
    end.

  Inductive LeakageI64 {width} {BW : Bitwidth width} {word: word.word width} : Type :=
  | Ld_leakage (addr: word)
  | Lwu_leakage (addr: word)
  | Addiw_leakage
  | Slliw_leakage (shamt : Z)
  | Srliw_leakage (shamt : Z)
  | Sraiw_leakage (shamt : Z)
  | Sd_leakage (addr: word)
  | Addw_leakage
  | Subw_leakage
  | Sllw_leakage (shamt : word)
  | Srlw_leakage (shamt : word)
  | Sraw_leakage (shamt : word)
  | InvalidI64_leakage.
  
  Definition leakage_of_instr_I64 {width} {BW : Bitwidth width} {word: word.word width}
    (getRegister : Register -> M word) (instr : InstructionI64) : M LeakageI64 :=
    match instr with
    | Ld _ rs1 oimm12 => addr <- getRegister rs1; Return (Ld_leakage (word.add addr (word.of_Z oimm12)))
    | Lwu _ rs1 oimm12 => addr <- getRegister rs1; Return (Lwu_leakage (word.add addr (word.of_Z oimm12)))
    | Addiw _ _ _ => Return Addiw_leakage
    | Slliw _ _ shamt => Return (Slliw_leakage shamt)
    | Srliw _ _ shamt => Return (Srliw_leakage shamt)
    | Sraiw _ _ shamt => Return (Sraiw_leakage shamt)
    | Sd rs1 _ simm12 => addr <- getRegister rs1; Return (Sd_leakage (word.add addr (word.of_Z simm12)))
    | Addw _ _ _ => Return Addw_leakage
    | Subw _ _ _ => Return Subw_leakage
    | Sllw _ _ rs2 => shamt <- getRegister rs2; Return (Sllw_leakage shamt)
    | Srlw _ _ rs2 => shamt <- getRegister rs2; Return (Srlw_leakage shamt)
    | Sraw _ _ rs2 => shamt <- getRegister rs2; Return (Sraw_leakage shamt)
    | InvalidI64 => Return InvalidI64_leakage
    end.

  Inductive LeakageI {width} {BW : Bitwidth width} {word: word.word width} : Type :=
  | Lb_leakage (addr: word)
  | Lh_leakage (addr: word)
  | Lw_leakage (addr: word)
  | Lbu_leakage (addr: word)
  | Lhu_leakage (addr: word)
  | Fence_leakage (* unsure about this one. *)
  | Fence_i_leakage
  | Addi_leakage
  | Slli_leakage (shamt : Z)
  | Slti_leakage
  | Sltiu_leakage
  | Xori_leakage
  | Ori_leakage
  | Andi_leakage
  | Srli_leakage (shamt : Z)
  | Srai_leakage (shamt : Z)
  | Auipc_leakage
  | Sb_leakage (addr: word)
  | Sh_leakage (addr: word)
  | Sw_leakage (addr: word)
  | Add_leakage
  | Sub_leakage
  | Sll_leakage (shamt : word)
  | Slt_leakage
  | Sltu_leakage
  | Xor_leakage
  | Srl_leakage (shamt : word)
  | Sra_leakage (shamt : word)
  | Or_leakage
  | And_leakage
  | Lui_leakage
  | Beq_leakage (branch: bool)
  | Bne_leakage (branch: bool)
  | Blt_leakage (branch: bool)
  | Bge_leakage (branch: bool)
  | Bltu_leakage (branch: bool)
  | Bgeu_leakage (branch: bool)
  | Jalr_leakage
  | Jal_leakage
  | InvalidI_leakage.

  Definition leakage_of_instr_I {width} {BW : Bitwidth width} {word: word.word width}
    (getRegister : Register -> M word) (instr : InstructionI) : M LeakageI :=
    match instr with
    | Lb _ rs1 oimm12 => rs1_val <- getRegister rs1; Return (Lb_leakage (word.add rs1_val (word.of_Z oimm12)))
    | Lh _ rs1 oimm12 => rs1_val <- getRegister rs1; Return (Lh_leakage (word.add rs1_val (word.of_Z oimm12)))
    | Lw _ rs1 oimm12 => rs1_val <- getRegister rs1; Return (Lw_leakage (word.add rs1_val (word.of_Z oimm12)))
    | Lbu _ rs1 oimm12 => rs1_val <- getRegister rs1; Return (Lbu_leakage (word.add rs1_val (word.of_Z oimm12)))
    | Lhu _ rs1 oimm12 => rs1_val <- getRegister rs1; Return (Lhu_leakage (word.add rs1_val (word.of_Z oimm12)))
    | Fence _ _ => Return Fence_leakage
    | Fence_i => Return Fence_i_leakage
    | Addi _ _ _ => Return Addi_leakage
    | Slli _ _ shamt => Return (Slli_leakage shamt)
    | Slti _ _ _ => Return Slti_leakage
    | Sltiu _ _ _ => Return Sltiu_leakage
    | Xori _ _ _ => Return Xori_leakage
    | Ori _ _ _ => Return Ori_leakage
    | Andi _ _ _ => Return Andi_leakage
    | Srli _ _ shamt => Return (Srli_leakage shamt)
    | Srai _ _ shamt => Return (Srai_leakage shamt)
    | Auipc _ _ => Return Auipc_leakage
    | Sb rs1 _ simm12 => rs1_val <- getRegister rs1; Return (Sb_leakage (word.add rs1_val (word.of_Z simm12)))
    | Sh rs1 _ simm12 => rs1_val <- getRegister rs1; Return (Sh_leakage (word.add rs1_val (word.of_Z simm12)))
    | Sw rs1 _ simm12 => rs1_val <- getRegister rs1; Return (Sw_leakage (word.add rs1_val (word.of_Z simm12)))
    | Add _ _ _ => Return Add_leakage
    | Sub _ _ _ => Return Sub_leakage
    | Sll _ _ rs2 => shamt <- getRegister rs2; Return (Sll_leakage shamt)
    | Slt _ _ _ => Return Slt_leakage
    | Sltu _ _ _ => Return Sltu_leakage
    | Xor _ _ _ => Return Xor_leakage
    | Srl _ _ rs2 => shamt <- getRegister rs2; Return (Srl_leakage shamt)
    | Sra _ _ rs2 => shamt <- getRegister rs2; Return (Sra_leakage shamt)
    | Or _ _ _ => Return Or_leakage
    | And _ _ _ => Return And_leakage
    | Lui _ _ => Return Lui_leakage
    | Beq rs1 rs2 _ => rs1_val <- getRegister rs1; rs2_val <- getRegister rs2; Return (Beq_leakage (word.eqb rs1_val rs2_val))
    | Bne rs1 rs2 _ => rs1_val <- getRegister rs1; rs2_val <- getRegister rs2; Return (Bne_leakage (negb (word.eqb rs1_val rs2_val)))
    | Blt rs1 rs2 _ => rs1_val <- getRegister rs1; rs2_val <- getRegister rs2; Return (Blt_leakage (word.lts rs1_val rs2_val))
    | Bge rs1 rs2 _ => rs1_val <- getRegister rs1; rs2_val <- getRegister rs2; Return (Bge_leakage (negb (word.lts rs1_val rs2_val)))
    | Bltu rs1 rs2 _ => rs1_val <- getRegister rs1; rs2_val <- getRegister rs2; Return (Bltu_leakage (word.ltu rs1_val rs2_val))
    | Bgeu rs1 rs2 _ => rs1_val <- getRegister rs1; rs2_val <- getRegister rs2; Return (Bgeu_leakage (negb (word.ltu rs1_val rs2_val)))
    | Jalr _ _ _ => Return Jalr_leakage
    | Jal _ _ => Return Jal_leakage
    | InvalidI => Return InvalidI_leakage
    end.

  Inductive LeakageF64 : Type :=.
  
  Inductive LeakageF {width} {BW : Bitwidth width} {word: word.word width} : Type :=
  | Flw_leakage (addr: word)
  | Fsw_leakage (addr: word)
  | Fmadd_s_leakage
  | Fmsub_s_leakage
  | Fnmsub_s_leakage
  | Fnmadd_s_leakage
  | Fadd_s_leakage
  | Fsub_s_leakage
  | Fmul_s_leakage
  | Fdiv_s_leakage
  | Fsqrt_s_leakage
  | Fsgnj_s_leakage
  | Fsgnjn_s_leakage
  | Fsgnjx_s_leakage
  | Fmin_s_leakage
  | Fmax_s_leakage
  | Fcvt_w_s_leakage
  | Fcvt_wu_s_leakage
  | Fmv_x_w_leakage
  | Feq_s_leakage
  | Flt_s_leakage
  | Fle_s_leakage
  | Fclass_s_leakage
  | Fcvt_s_w_leakage
  | Fcvt_s_wu_leakage
  | Fmv_w_x_leakage
  | InvalidF_leakage.

  Definition leakage_of_instr_F {width} {BW : Bitwidth width} {word: word.word width}
    (getRegister : Register -> M word) (instr : InstructionF) : M LeakageF :=
    match instr with
    | Flw _ rs1 oimm12 => rs1_val <- getRegister rs1; Return (Flw_leakage (word.add rs1_val (word.of_Z oimm12)))
    | Fsw rs1 _ simm12 => rs1_val <- getRegister rs1; Return (Fsw_leakage (word.add rs1_val (word.of_Z simm12)))
    | Fmadd_s _ _ _ _ _ => Return Fmadd_s_leakage
    | Fmsub_s _ _ _ _ _ => Return Fmsub_s_leakage
    | Fnmsub_s _ _ _ _ _ => Return Fnmsub_s_leakage
    | Fnmadd_s _ _ _ _ _ => Return Fnmadd_s_leakage
    | Fadd_s _ _ _ _ => Return Fadd_s_leakage
    | Fsub_s _ _ _ _ => Return Fsub_s_leakage
    | Fmul_s _ _ _ _ => Return Fmul_s_leakage
    | Fdiv_s _ _ _ _ => Return Fdiv_s_leakage
    | Fsqrt_s _ _ _ => Return Fsqrt_s_leakage
    | Fsgnj_s _ _ _ => Return Fsgnj_s_leakage
    | Fsgnjn_s _ _ _ => Return Fsgnjn_s_leakage
    | Fsgnjx_s _ _ _ => Return Fsgnjx_s_leakage
    | Fmin_s _ _ _ => Return Fmin_s_leakage
    | Fmax_s _ _ _ => Return Fmax_s_leakage
    | Fcvt_w_s _ _ _ => Return Fcvt_w_s_leakage
    | Fcvt_wu_s _ _ _ => Return Fcvt_wu_s_leakage
    | Fmv_x_w _ _ => Return Fmv_x_w_leakage
    | Feq_s _ _ _ => Return Feq_s_leakage
    | Flt_s _ _ _ => Return Flt_s_leakage
    | Fle_s _ _ _ => Return Fle_s_leakage
    | Fclass_s _ _ => Return Fclass_s_leakage
    | Fcvt_s_w _ _ _ => Return Fcvt_s_w_leakage
    | Fcvt_s_wu _ _ _ => Return Fcvt_s_wu_leakage
    | Fmv_w_x _ _ => Return Fmv_w_x_leakage
    | InvalidF => Return InvalidF_leakage
    end.

  Inductive LeakageCSR : Type :=.
  
  Inductive LeakageA64 : Type :=.

  Inductive LeakageA : Type :=.

  Inductive LeakageEvent {width} {BW : Bitwidth width} {word: word.word width} : Type :=
  | anything {X : Type} (x : X)
  | fetchInstr (address : word)
  | ILeakage (iLeakage : LeakageI)
  | MLeakage (mLeakage : LeakageM)
  | ALeakage (aLeakage : LeakageA)
  | FLeakage (fLeakage : LeakageF)
  | I64Leakage (i64Leakage : LeakageI64)
  | M64Leakage (m64Leakage : LeakageM64)
  | A64Leakage (a64Leakage : LeakageA64)
  | F64Leakage (f64Leakage : LeakageF64)
  | CSRLeakage (csrLeakage : LeakageCSR)
  | InvalidLeakage.
  
  Definition leakage_of_instr {width} {BW : Bitwidth width} {word: word.word width}
    (getRegister : Register -> M word) (instr : Instruction) : M (option LeakageEvent) :=
    match instr with
    | IInstruction instr => l <- leakage_of_instr_I getRegister instr; Return (Some (ILeakage l))
    | MInstruction instr => l <- leakage_of_instr_M getRegister instr; Return (Some (MLeakage l))
    | AInstruction instr => Return None
    | FInstruction instr => l <- leakage_of_instr_F getRegister instr; Return (Some (FLeakage l))
    | I64Instruction instr => l <- leakage_of_instr_I64 getRegister instr; Return (Some (I64Leakage l))
    | M64Instruction instr => l <- leakage_of_instr_M64 getRegister instr; Return (Some (M64Leakage l))
    | A64Instruction instr => Return None
    | F64Instruction instr => Return None
    | CSRInstruction instr => Return None
    | InvalidInstruction _ => Return (Some InvalidLeakage)
    end.

End WithMonad.

Definition concrete_leakage_of_instr {width} {BW: Bitwidth width} {word: word.word width} :=
  @leakage_of_instr (fun T => T) _ width BW word.
