Require Import Coq.ZArith.BinInt.
Require Import riscv.util.NameWithEq.
Require Import riscv.RiscvBitWidths.
Require Import riscv.util.Monads.
Require Import riscv.Utility.
Require Import riscv.Decode.
Require Import riscv.Program.

Local Open Scope Z.
Local Open Scope alu_scope.
Local Open Scope bool_scope.

Section Riscv.

  Context {Name: NameWithEq}. (* register name *)
  Let Register := @name Name.
  Existing Instance eq_name_dec.

  Context {B: RiscvBitWidths}.

  Context {M: Type -> Type}.
  Context {MM: Monad M}.
  Context {t: Set}.
  Context {MW: MachineWidth t}.
  Context {MP: MonadPlus M}.
  Context {RVP: RiscvProgram M t}.
  Context {RVS: RiscvState M t}.

  Definition execute(i: Instruction): M unit :=
    match i with
    (* begin ast *)
    | Lui rd imm20 =>
        setRegister rd (fromImm imm20)
    | Auipc rd oimm20 =>
        pc <- getPC;
        setRegister rd (fromImm oimm20 + pc)
    | Jal rd jimm20 =>
        pc <- getPC;
        let newPC := pc + (fromImm jimm20) in
        if (rem newPC four /= zero)
          then raiseException zero zero
          else (
            setRegister rd (pc + four);;
            setPC newPC)
    | Jalr rd rs1 oimm12 =>
        x <- getRegister rs1;
        pc <- getPC;
        let newPC := x + fromImm oimm12 in
        if (rem newPC four /= zero)
          then raiseException zero zero
          else (
            setRegister rd (pc + four);;
            setPC newPC)
    | Beq rs1 rs2 sbimm12 =>
        x <- getRegister rs1;
        y <- getRegister rs2;
        pc <- getPC;
        when (x == y) (
          let newPC := (pc + fromImm sbimm12) in
          if (rem newPC four /= zero)
            then raiseException zero zero
            else setPC newPC)
    | Bne rs1 rs2 sbimm12 =>
        x <- getRegister rs1;
        y <- getRegister rs2;
        pc <- getPC;
        when (x /= y) (
          let addr := (pc + fromImm sbimm12) in
          if (rem addr four /= zero)
            then raiseException zero zero
            else setPC addr)
    | Blt rs1 rs2 sbimm12 =>
        x <- getRegister rs1;
        y <- getRegister rs2;
        pc <- getPC;
        when (x < y) (
          let addr := (pc + fromImm sbimm12) in
          if (rem addr four /= zero)
            then raiseException zero zero
            else setPC addr)
    | Bge rs1 rs2 sbimm12 =>
        x <- getRegister rs1;
        y <- getRegister rs2;
        pc <- getPC;
        when (x >= y) (
          let addr := (pc + fromImm sbimm12) in
          if (rem addr four /= zero)
            then raiseException zero zero
            else setPC addr)
    | Bltu rs1 rs2 sbimm12 =>
        x <- getRegister rs1;
        y <- getRegister rs2;
        pc <- getPC;
        when ((ltu x y)) (
          let addr := (pc + fromImm sbimm12) in
          if (rem addr four /= zero)
            then raiseException zero zero
            else setPC addr)
    | Bgeu rs1 rs2 sbimm12 =>
        x <- getRegister rs1;
        y <- getRegister rs2;
        pc <- getPC;
        when (negb (ltu x y)) (
          let addr := (pc + fromImm sbimm12) in
          if (rem addr four /= zero)
            then raiseException zero zero
            else setPC addr)
    | Lb rd rs1 oimm12 =>
        a <- getRegister rs1;
        addr <- translate Load one (a + fromImm oimm12);
        x <- loadByte addr;
        setRegister rd (int8ToReg x)
    | Lh rd rs1 oimm12 =>
        a <- getRegister rs1;
        addr <- translate Load two (a + fromImm oimm12);
        x <- loadHalf addr;
        setRegister rd (int16ToReg x)
    | Lw rd rs1 oimm12 =>
        a <- getRegister rs1;
        addr <- translate Load four (a + fromImm oimm12);
        x <- loadWord addr;
        setRegister rd (int32ToReg x)
    | Lbu rd rs1 oimm12 =>
        a <- getRegister rs1;
        addr <- translate Load one (a + fromImm oimm12);
        x <- loadByte addr;
        setRegister rd (uInt8ToReg x)
    | Lhu rd rs1 oimm12 =>
        a <- getRegister rs1;
        addr <- translate Load two (a + fromImm oimm12);
        x <- loadHalf addr;
        setRegister rd (uInt16ToReg x)
    | Sb rs1 rs2 simm12 =>
        a <- getRegister rs1;
        addr <- translate Store one (a + fromImm simm12);
        x <- getRegister rs2;
        storeByte addr (regToInt8 x)
    | Sh rs1 rs2 simm12 =>
        a <- getRegister rs1;
        addr <- translate Store two (a + fromImm simm12);
        x <- getRegister rs2;
        storeHalf addr (regToInt16 x)
    | Sw rs1 rs2 simm12 =>
        a <- getRegister rs1;
        addr <- translate Store four (a + fromImm simm12);
        x <- getRegister rs2;
        storeWord addr (regToInt32 x)
    | Addi rd rs1 imm12 =>
        x <- getRegister rs1;
        setRegister rd (x + fromImm imm12)
    | Slti rd rs1 imm12 =>
        x <- getRegister rs1;
        setRegister rd (if x < (fromImm imm12) then one else zero)
    | Sltiu rd rs1 imm12 =>
        x <- getRegister rs1;
        setRegister rd (if (ltu x (fromImm imm12)) then one else zero)
    | Xori rd rs1 imm12 =>
        x <- getRegister rs1;
        setRegister rd (xor x (fromImm imm12))
    | Ori rd rs1 imm12 =>
        x <- getRegister rs1;
        setRegister rd (x <|> (fromImm imm12))
    | Andi rd rs1 imm12 =>
        x <- getRegister rs1;
        setRegister rd (x <&> (fromImm imm12))
    | Slli rd rs1 shamt6 =>
        x <- getRegister rs1;
        setRegister rd (sll x (regToShamt (fromImm shamt6 : t)))
    | Srli rd rs1 shamt6 =>
        x <- getRegister rs1;
        setRegister rd (srl x (regToShamt (fromImm shamt6 : t)))
    | Srai rd rs1 shamt6 =>
        x <- getRegister rs1;
        setRegister rd (sra x (regToShamt (fromImm shamt6 : t)))
    | Add rd rs1 rs2 =>
        x <- getRegister rs1;
        y <- getRegister rs2;
        setRegister rd (x + y)
    | Sub rd rs1 rs2 =>
        x <- getRegister rs1;
        y <- getRegister rs2;
        setRegister rd (x - y)
    | Sll rd rs1 rs2 =>
        x <- getRegister rs1;
        y <- getRegister rs2;
        setRegister rd (sll x (regToShamt y))
    | Slt rd rs1 rs2 =>
        x <- getRegister rs1;
        y <- getRegister rs2;
        setRegister rd (if x < y then one else zero)
    | Sltu rd rs1 rs2 =>
        x <- getRegister rs1;
        y <- getRegister rs2;
        setRegister rd (if (ltu x y) then one else zero)
    | Xor rd rs1 rs2 =>
        x <- getRegister rs1;
        y <- getRegister rs2;
        setRegister rd (xor x y)
    | Or rd rs1 rs2 =>
        x <- getRegister rs1;
        y <- getRegister rs2;
        setRegister rd (x <|> y)
    | Srl rd rs1 rs2 =>
        x <- getRegister rs1;
        y <- getRegister rs2;
        setRegister rd (srl x (regToShamt y))
    | Sra rd rs1 rs2 =>
        x <- getRegister rs1;
        y <- getRegister rs2;
        setRegister rd (sra x (regToShamt y))
    | And rd rs1 rs2 =>
        x <- getRegister rs1;
        y <- getRegister rs2;
        setRegister rd (x <&> y)
    (* end ast *)
    | _ => mzero
    end.

End Riscv.
