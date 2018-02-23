Require Import Coq.ZArith.BinInt.
Require Import bbv.WordScope.
Require Import riscv.util.NameWithEq.
Require Import riscv.RiscvBitWidths.
Require Import riscv.util.Monad.
Require Import riscv.Decode.
Require Import riscv.Program.

Instance icId{t: Set}: IntegralConversion t t := {|
  fromIntegral := id
|}.

Section Riscv.

  Context {Name: NameWithEq}. (* register name *)
  Notation Register := (@name Name).
  Existing Instance eq_name_dec.

  Context {B: RiscvBitWidths}.

  Context {t u: Set}.

  Context {A: Alu t u}.

  Context {ic8: IntegralConversion (word 8) t}.

  Context {icZ: IntegralConversion Z t}.

  Definition execute{M: Type -> Type}{MM: Monad M}{RVS: RiscvState M}(i: Instruction): M unit :=
    match i with
    (* begin ast *)
    | Lui rd imm20 =>
        setRegister rd imm20
    | Auipc rd oimm20 =>
        pc <- getPC;
        setRegister rd (fromIntegral oimm20 + pc)
    | Jal rd jimm20 => Return tt (*
        pc <- getPC;
        let newPC = pc + (fromIntegral jimm20)
        if dec ((mod newPC 4 /= 0))
          then raiseException 0 0
          else (do
            setRegister rd (fromIntegral pc + 4)
            setPC newPC)
  *)| Jalr rd rs1 oimm12 => Return tt (*
        x <- getRegister rs1;
        pc <- getPC;
        let newPC = x + fromIntegral oimm12
        if dec ((mod newPC 4 /= 0))
          then raiseException 0 0
          else (do
            setRegister rd (fromIntegral pc + 4)
            setPC newPC)
  *)| Beq rs1 rs2 sbimm12 => Return tt (*
        x <- getRegister rs1;
        y <- getRegister rs2;
        pc <- getPC;
        when (x == y) (do
          let newPC = (pc + fromIntegral sbimm12)
          if dec ((mod newPC 4 /= 0))
            then raiseException 0 0
            else setPC newPC)
  *)| Bne rs1 rs2 sbimm12 => Return tt (*
        x <- getRegister rs1;
        y <- getRegister rs2;
        pc <- getPC;
        when (x /= y) (do
          let addr = (pc + fromIntegral sbimm12)
          if dec ((mod addr 4 /= 0))
            then raiseException 0 0
            else setPC addr)
  *)| Blt rs1 rs2 sbimm12 => Return tt (*
        x <- getRegister rs1;
        y <- getRegister rs2;
        pc <- getPC;
        when (x < y) (do
          let addr = (pc + fromIntegral sbimm12)
          if dec ((mod addr 4 /= 0))
            then raiseException 0 0
            else setPC addr)
  *)| Bge rs1 rs2 sbimm12 => Return tt (*
        x <- getRegister rs1;
        y <- getRegister rs2;
        pc <- getPC;
        when (x >= y) (do
          let addr = (pc + fromIntegral sbimm12)
          if dec ((mod addr 4 /= 0))
            then raiseException 0 0
            else setPC addr)
  *)| Bltu rs1 rs2 sbimm12 => Return tt (*
        x <- getRegister rs1;
        y <- getRegister rs2;
        pc <- getPC;
        when ((unsigned x) < (unsigned y)) (do
          let addr = (pc + fromIntegral sbimm12)
          if dec ((mod addr 4 /= 0))
            then raiseException 0 0
            else setPC addr)
  *)| Bgeu rs1 rs2 sbimm12 => Return tt (*
        x <- getRegister rs1;
        y <- getRegister rs2;
        pc <- getPC;
        when ((unsigned x) >= (unsigned y)) (do
          let addr = (pc + fromIntegral sbimm12)
          if dec ((mod addr 4 /= 0))
            then raiseException 0 0
            else setPC addr)
  *)| Lb rd rs1 oimm12 => Return tt (*
        a <- getRegister rs1;
        withTranslation Load 1 (a + fromIntegral oimm12)
          (\addr -> do
              x <- loadByte addr;
              setRegister rd x)
  *)| Lh rd rs1 oimm12 => Return tt (*
        a <- getRegister rs1;
        withTranslation Load 2 (a + fromIntegral oimm12)
          (\addr -> do
              x <- loadHalf addr;
              setRegister rd x)
  *)| Lw rd rs1 oimm12 => Return tt (*
        a <- getRegister rs1;
        withTranslation Load 4 (a + fromIntegral oimm12)
          (\addr -> do
              x <- loadWord addr;
              setRegister rd x)
  *)| Lbu rd rs1 oimm12 => Return tt (*
        a <- getRegister rs1;
        withTranslation Load 1 (a + fromIntegral oimm12)
          (\addr -> do
              x <- loadByte addr;
              setRegister rd (unsigned x))
  *)| Lhu rd rs1 oimm12 => Return tt (*
        a <- getRegister rs1;
        withTranslation Load 2 (a + fromIntegral oimm12)
          (\addr -> do
              x <- loadHalf addr;
              setRegister rd (unsigned x))
  *)| Sb rs1 rs2 simm12 => Return tt (*
        a <- getRegister rs1;
        withTranslation Store 1 (a + fromIntegral simm12)
          (\addr -> do
              x <- getRegister rs2;
              storeByte addr x)
  *)| Sh rs1 rs2 simm12 => Return tt (*
        a <- getRegister rs1;
        withTranslation Store 2 (a + fromIntegral simm12)
          (\addr -> do
              x <- getRegister rs2;
              storeHalf addr x)
  *)| Sw rs1 rs2 simm12 => Return tt (*
        a <- getRegister rs1;
        withTranslation Store 4 (a + fromIntegral simm12)
          (\addr -> do
              x <- getRegister rs2;
              storeWord addr x)
  *)| Addi rd rs1 imm12 =>
        x <- getRegister rs1;
        setRegister rd (x + fromIntegral imm12)
    | Slti rd rs1 imm12 => Return tt (*
        x <- getRegister rs1;
        setRegister rd (if dec(x < fromIntegral imm12) then 1 else 0)
  *)| Sltiu rd rs1 imm12 => Return tt (*
        x <- getRegister rs1;
        setRegister rd (if dec((unsigned x) < (fromIntegral imm12 : u)) then 1 else 0)
  *)| Xori rd rs1 imm12 =>
        x <- getRegister rs1;
        setRegister rd (xor x (fromIntegral imm12))
    | Ori rd rs1 imm12 =>
        x <- getRegister rs1;
        setRegister rd (x <|> (fromIntegral imm12))
    | Andi rd rs1 imm12 =>
        x <- getRegister rs1;
        setRegister rd (x <&> (fromIntegral imm12))
    | Slli rd rs1 shamt6 => Return tt (*
        x <- getRegister rs1;
        setRegister rd (slli x shamt6)
  *)| Srli rd rs1 shamt6 => Return tt (*
        x <- getRegister rs1;
        setRegister rd (srli x shamt6)
  *)| Srai rd rs1 shamt6 => Return tt (*
        x <- getRegister rs1;
        setRegister rd (srai x shamt6)
  *)| Add rd rs1 rs2 =>
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
        setRegister rd (sll x y)
    | Slt rd rs1 rs2 => Return tt (*
        x <- getRegister rs1;
        y <- getRegister rs2;
        setRegister rd (if dec(x < y) then 1 else 0)
  *)| Sltu rd rs1 rs2 => Return tt (*
        x <- getRegister rs1;
        y <- getRegister rs2;
        setRegister rd (if dec((unsigned x) < (unsigned y)) then 1 else 0)
  *)| Xor rd rs1 rs2 =>
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
        setRegister rd (srl x y)
    | Sra rd rs1 rs2 =>
        x <- getRegister rs1;
        y <- getRegister rs2;
        setRegister rd (sra x y)
    | And rd rs1 rs2 =>
        x <- getRegister rs1;
        y <- getRegister rs2;
        setRegister rd (x <&> y)
    (* end ast *)
    | _ => Return tt
    end.

End Riscv.
