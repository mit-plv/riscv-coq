Require Import Coq.ZArith.BinInt.
Require Import riscv.util.NameWithEq.
Require Import riscv.RiscvBitWidths.
Require Import riscv.util.StateMonad.
Require Import riscv.Utility.
Require Import riscv.NoVirtualMemory.
Require Import riscv.Decode.
Require Import riscv.Program.

Local Open Scope Z.
Local Open Scope alu_scope.
Local Open Scope bool_scope.

Section Riscv.

  Context {Name: NameWithEq}. (* register name *)
  Notation Register := (@name Name).
  Existing Instance eq_name_dec.

  Context {B: RiscvBitWidths}.

  Context {t: Set}.

  Context {MW: MachineWidth t}.

  Definition execute{M: Type -> Type}{MM: Monad M}{MP: MonadPlus M}{RVS: RiscvState M}
    (i: Instruction): M unit :=
    match i with
    (* begin ast *)
    | Lwu rd rs1 oimm12 =>
        a <- getRegister rs1;
        addr <- translate Load four (a + fromImm oimm12);
        x <- loadWord addr;
        setRegister rd (uInt32ToReg x)
    | Ld rd rs1 oimm12 =>
        a <- getRegister rs1;
        addr <- translate Load eight (a + fromImm oimm12);
        x <- loadDouble addr;
        setRegister rd (int64ToReg x)
    | Sd rs1 rs2 simm12 =>
        a <- getRegister rs1;
        addr <- translate Store eight (a + fromImm simm12);
        x <- getRegister rs2;
        storeDouble addr (regToInt64 x)
    | Addiw rd rs1 imm12 =>
        x <- getRegister rs1;
        setRegister rd (s32 (x + fromImm imm12))
    | Slliw rd rs1 shamt5 =>
        x <- getRegister rs1;
        setRegister rd (s32 (sll x (regToShamt5 (fromImm shamt5 : t))))
    | Srliw rd rs1 shamt5 =>
        x <- getRegister rs1;
        setRegister rd (s32 (srl (u32 x) (regToShamt5 (fromImm shamt5 : t))))
    | Sraiw rd rs1 shamt5 =>
        x <- getRegister rs1;
        setRegister rd (s32 (sra (s32 x) (regToShamt5 (fromImm shamt5 : t))))
    | Addw rd rs1 rs2 =>
        x <- getRegister rs1;
        y <- getRegister rs2;
        setRegister rd (s32 (x + y))
    | Subw rd rs1 rs2 =>
        x <- getRegister rs1;
        y <- getRegister rs2;
        setRegister rd (s32 (x - y))
    | Sllw rd rs1 rs2 =>
        x <- getRegister rs1;
        y <- getRegister rs2;
        setRegister rd (s32 (sll x (regToShamt5 y)))
    | Srlw rd rs1 rs2 =>
        x <- getRegister rs1;
        y <- getRegister rs2;
        setRegister rd (s32 (srl (u32 x) (regToShamt5 y)))
    | Sraw rd rs1 rs2 =>
        x <- getRegister rs1;
        y <- getRegister rs2;
        setRegister rd (s32 (sra (s32 x) (regToShamt5 y)))
    (* end ast *)
    | _ => mzero
    end.

End Riscv.
