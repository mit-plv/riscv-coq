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

Local Open Scope Z.
Local Open Scope alu_scope.

Section Riscv.

  Context {Name: NameWithEq}. (* register name *)
  Notation Register := (@name Name).
  Existing Instance eq_name_dec.

  Context {B: RiscvBitWidths}.

  Context {t u: Set}.

  Context {A: Alu t u}.

  Context {ic8: IntegralConversion (word 8) t}.

  Context {icZt: IntegralConversion Z t}.

  Context {icZu: IntegralConversion Z u}.

  (* TODO *)
  Definition raiseException{M: Type -> Type}{MM: Monad M}(x1 x2: t): M unit := Return tt.

  Definition four: t := one + one + one + one.

  Notation "'when' a b" := (if a then b else Return tt) (at level 60, a at level 0, b at level 0).

  Definition execute{M: Type -> Type}{MM: Monad M}{RVS: RiscvState M}(i: Instruction): M unit :=
    match i with
    (* begin ast *)
    | Lui rd imm20 =>
        setRegister rd imm20
    | Auipc rd oimm20 =>
        pc <- getPC;
        setRegister rd (fromIntegral oimm20 + pc)
    | Jal rd jimm20 =>
        pc <- getPC;
        let newPC := pc + (fromIntegral jimm20) in
        if (rem newPC four /= zero)
          then raiseException zero zero
          else (
            setRegister rd (fromIntegral pc + four);;
            setPC newPC)
    | Jalr rd rs1 oimm12 =>
        x <- getRegister rs1;
        pc <- getPC;
        let newPC := x + fromIntegral oimm12 in
        if (rem newPC four /= zero)
          then raiseException zero zero
          else (
            setRegister rd (fromIntegral pc + four);;
            setPC newPC)
    | Beq rs1 rs2 sbimm12 =>
        x <- getRegister rs1;
        y <- getRegister rs2;
        pc <- getPC;
        when (x == y) (
          let newPC := (pc + fromIntegral sbimm12) in
          if (rem newPC four /= zero)
            then raiseException zero zero
            else setPC newPC)
    | Bne rs1 rs2 sbimm12 =>
        x <- getRegister rs1;
        y <- getRegister rs2;
        pc <- getPC;
        when (x /= y) (
          let addr := (pc + fromIntegral sbimm12) in
          if (rem addr four /= zero)
            then raiseException zero zero
            else setPC addr)
    | Blt rs1 rs2 sbimm12 =>
        x <- getRegister rs1;
        y <- getRegister rs2;
        pc <- getPC;
        when (x < y) (
          let addr := (pc + fromIntegral sbimm12) in
          if (rem addr four /= zero)
            then raiseException zero zero
            else setPC addr)
    | Bge rs1 rs2 sbimm12 =>
        x <- getRegister rs1;
        y <- getRegister rs2;
        pc <- getPC;
        when (x >= y) (
          let addr := (pc + fromIntegral sbimm12) in
          if (rem addr four /= zero)
            then raiseException zero zero
            else setPC addr)
    | Bltu rs1 rs2 sbimm12 =>
        x <- getRegister rs1;
        y <- getRegister rs2;
        pc <- getPC;
        when ((unsigned x) <u (unsigned y)) (
          let addr := (pc + fromIntegral sbimm12) in
          if (rem addr four /= zero)
            then raiseException zero zero
            else setPC addr)
    | Bgeu rs1 rs2 sbimm12 =>
        x <- getRegister rs1;
        y <- getRegister rs2;
        pc <- getPC;
        when ((unsigned x) >=u (unsigned y)) (
          let addr := (pc + fromIntegral sbimm12) in
          if (rem addr four /= zero)
            then raiseException zero zero
            else setPC addr)
    | Lb rd rs1 oimm12 => Return tt (*
        a <- getRegister rs1;
        withTranslation Load one (a + fromIntegral oimm12)
          (\addr -> 
              x <- loadByte addr;
              setRegister rd x)
  *)| Lh rd rs1 oimm12 => Return tt (*
        a <- getRegister rs1;
        withTranslation Load 2 (a + fromIntegral oimm12)
          (\addr -> 
              x <- loadHalf addr;
              setRegister rd x)
  *)| Lw rd rs1 oimm12 => Return tt (*
        a <- getRegister rs1;
        withTranslation Load four (a + fromIntegral oimm12)
          (\addr -> 
              x <- loadWord addr;
              setRegister rd x)
  *)| Lbu rd rs1 oimm12 => Return tt (*
        a <- getRegister rs1;
        withTranslation Load one (a + fromIntegral oimm12)
          (\addr -> 
              x <- loadByte addr;
              setRegister rd (unsigned x))
  *)| Lhu rd rs1 oimm12 => Return tt (*
        a <- getRegister rs1;
        withTranslation Load 2 (a + fromIntegral oimm12)
          (\addr -> 
              x <- loadHalf addr;
              setRegister rd (unsigned x))
  *)| Sb rs1 rs2 simm12 => Return tt (*
        a <- getRegister rs1;
        withTranslation Store one (a + fromIntegral simm12)
          (\addr -> 
              x <- getRegister rs2;
              storeByte addr x)
  *)| Sh rs1 rs2 simm12 => Return tt (*
        a <- getRegister rs1;
        withTranslation Store 2 (a + fromIntegral simm12)
          (\addr -> 
              x <- getRegister rs2;
              storeHalf addr x)
  *)| Sw rs1 rs2 simm12 => Return tt (*
        a <- getRegister rs1;
        withTranslation Store four (a + fromIntegral simm12)
          (\addr -> 
              x <- getRegister rs2;
              storeWord addr x)
  *)| Addi rd rs1 imm12 =>
        x <- getRegister rs1;
        setRegister rd (x + fromIntegral imm12)
    | Slti rd rs1 imm12 => Return tt (*
        x <- getRegister rs1;
        setRegister rd (if x < fromIntegral imm12 then one else zero)
  *)| Sltiu rd rs1 imm12 =>
        x <- getRegister rs1;
        setRegister rd (if (unsigned x) <u (fromIntegral imm12 : u) then one else zero)
    | Xori rd rs1 imm12 =>
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
    | Slt rd rs1 rs2 =>
        x <- getRegister rs1;
        y <- getRegister rs2;
        setRegister rd (if x < y then one else zero)
    | Sltu rd rs1 rs2 =>
        x <- getRegister rs1;
        y <- getRegister rs2;
        setRegister rd (if (unsigned x) <u (unsigned y) then one else zero)
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
