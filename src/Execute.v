Require Import Coq.ZArith.BinInt.
Require Import riscv.util.NameWithEq.
Require Import riscv.RiscvBitWidths.
Require Import riscv.util.Monad.
Require Import riscv.Utility.
Require Import riscv.NoVirtualMemory.
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

  Context {c: Convertible t u}.

  Context {ic8: IntegralConversion Int8 t}.
  Context {ic16: IntegralConversion Int16 t}.
  Context {ic32: IntegralConversion Int32 t}.

  Context {ic8': IntegralConversion t Int8}.
  Context {ic16': IntegralConversion t Int16}.
  Context {ic32': IntegralConversion t Int32}.

  Context {ic8u: IntegralConversion Word8 t}.
  Context {ic16u: IntegralConversion Word16 t}.
  Context {ic32u: IntegralConversion Word32 t}.

  Context {icZt: IntegralConversion Z t}.

  Context {icZu: IntegralConversion Z u}.

  Context {icut: IntegralConversion u t}.
  Context {ictu: IntegralConversion t u}.

  Context {m: MachineWidth t}.

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
        when ((ltu x y)) (
          let addr := (pc + fromIntegral sbimm12) in
          if (rem addr four /= zero)
            then raiseException zero zero
            else setPC addr)
    | Bgeu rs1 rs2 sbimm12 =>
        x <- getRegister rs1;
        y <- getRegister rs2;
        pc <- getPC;
        when (negb (ltu x y)) (
          let addr := (pc + fromIntegral sbimm12) in
          if (rem addr four /= zero)
            then raiseException zero zero
            else setPC addr)
    | Lb rd rs1 oimm12 =>
        a <- getRegister rs1;
        withTranslation Load one (a + fromIntegral oimm12)
          (fun addr => 
              x <- loadByte addr;
              setRegister rd x)
    | Lh rd rs1 oimm12 =>
        a <- getRegister rs1;
        withTranslation Load two (a + fromIntegral oimm12)
          (fun addr => 
              x <- loadHalf addr;
              setRegister rd x)
    | Lw rd rs1 oimm12 =>
        a <- getRegister rs1;
        withTranslation Load four (a + fromIntegral oimm12)
          (fun addr => 
              x <- loadWord addr;
              setRegister rd x)
    | Lbu rd rs1 oimm12 =>
        a <- getRegister rs1;
        withTranslation Load one (a + fromIntegral oimm12)
          (fun addr => 
              x <- loadByte addr;
              setRegister rd (unsigned x))
    | Lhu rd rs1 oimm12 =>
        a <- getRegister rs1;
        withTranslation Load two (a + fromIntegral oimm12)
          (fun addr => 
              x <- loadHalf addr;
              setRegister rd (unsigned x))
    | Sb rs1 rs2 simm12 =>
        a <- getRegister rs1;
        withTranslation Store one (a + fromIntegral simm12)
          (fun addr => 
              x <- getRegister rs2;
              storeByte addr (fromIntegral x))
    | Sh rs1 rs2 simm12 =>
        a <- getRegister rs1;
        withTranslation Store two (a + fromIntegral simm12)
          (fun addr => 
              x <- getRegister rs2;
              storeHalf addr (fromIntegral x))
    | Sw rs1 rs2 simm12 =>
        a <- getRegister rs1;
        withTranslation Store four (a + fromIntegral simm12)
          (fun addr => 
              x <- getRegister rs2;
              storeWord addr (fromIntegral x))
    | Addi rd rs1 imm12 =>
        x <- getRegister rs1;
        setRegister rd (x + fromIntegral imm12)
    | Slti rd rs1 imm12 =>
        x <- getRegister rs1;
        setRegister rd (if x < (fromIntegral imm12) then one else zero)
    | Sltiu rd rs1 imm12 =>
        x <- getRegister rs1;
        setRegister rd (if (ltu x imm12) then one else zero)
    | Xori rd rs1 imm12 =>
        x <- getRegister rs1;
        setRegister rd (xor x (fromIntegral imm12))
    | Ori rd rs1 imm12 =>
        x <- getRegister rs1;
        setRegister rd (x <|> (fromIntegral imm12))
    | Andi rd rs1 imm12 =>
        x <- getRegister rs1;
        setRegister rd (x <&> (fromIntegral imm12))
    | Slli rd rs1 shamt6 =>
        x <- getRegister rs1;
        setRegister rd (slli x shamt6)
    | Srli rd rs1 shamt6 =>
        x <- getRegister rs1;
        setRegister rd (srli x shamt6)
    | Srai rd rs1 shamt6 =>
        x <- getRegister rs1;
        setRegister rd (srai x shamt6)
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
        setRegister rd (sll x y)
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
