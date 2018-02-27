Require Import riscv.util.NameWithEq.
Require Import riscv.Utility.
Require Import Coq.ZArith.BinInt.

(* t will be instantiated with a signed type, u with an unsigned type.
   By default, all operations are on signed numbers. *)
Class Alu(t u: Set) := mkAlu {
  (* constants *)
  zero: t;
  one: t;

  (* arithmetic operations: *)
  add: t -> t -> t;
  sub: t -> t -> t;
  mul: t -> t -> t;
  div: t -> t -> t;
  rem: t -> t -> t;

  (* comparison operators: *)
  signed_less_than: t -> t -> bool;
  unsigned_less_than: u -> u -> bool;
  signed_eqb: t -> t -> bool;

  (* logical operations: *)
  shiftL: t -> Z -> t;
  signed_shiftR: t -> Z -> t; (* arithmetic shift *)
  unsigned_shiftR: u -> Z -> u; (* logic shift *)

  xor: t -> t -> t;
  or: t -> t -> t;
  and: t -> t -> t;
}.

Notation "a <|> b" := (or a b)  (at level 50, left associativity) : alu_scope.
Notation "a <&> b" := (and a b) (at level 40, left associativity) : alu_scope.
Notation "a + b"   := (add a b) (at level 50, left associativity) : alu_scope.
Notation "a - b"   := (sub a b) (at level 50, left associativity) : alu_scope.

Notation "a /= b" := (negb (signed_eqb a b))        (at level 70, no associativity) : alu_scope.
Notation "a == b" := (signed_eqb a b)               (at level 70, no associativity) : alu_scope.
Notation "a < b"  := (signed_less_than a b)         (at level 70, no associativity) : alu_scope.
Notation "a >= b" := (negb (signed_less_than a b))  (at level 70, no associativity) : alu_scope.

Definition ltu{t u s: Set}{A: Alu t u}{c: Convertible t u}{ic: IntegralConversion s u}
  (x: t)(y: s): bool := unsigned_less_than (unsigned x) (fromIntegral y: u).

Section Constants.
  Context {t u: Set}.
  Context {A: Alu t u}.

  Local Open Scope alu_scope.

  Definition two: t := one + one.

  Definition four: t := two + two.

End Constants.

Section Shifts.

  Context {t u: Set}.
  Context {A: Alu t u}.
  Context {c: Convertible t u}.
  Context {m: MachineWidth t}.
  Context {ic0: IntegralConversion Z t}.

  Definition slli(x: t)(shamt6: Z): t :=
    shiftL x (shiftBits (fromIntegral shamt6: t)).

  Definition srli(x: t)(shamt6: Z): u :=
    unsigned_shiftR ((unsigned x) : u) (shiftBits (fromIntegral shamt6 : t)).

  Definition srai(x: t)(shamt6: Z): t :=
    signed_shiftR x (shiftBits (fromIntegral shamt6 : t)).

  Definition sll(x y: t): t := shiftL x (shiftBits y).

  Definition srl(x y: t): u := unsigned_shiftR (unsigned x) (shiftBits y).

  Definition sra(x y: t): t := signed_shiftR x (shiftBits y).

End Shifts.

Section Riscv.

  Context {Name: NameWithEq}. (* register name *)
  Notation Register := (@name Name).

  Class RiscvState(M: Type -> Type){t u: Set}{A: Alu t u} := mkRiscvState {
    getRegister: Register -> M t;
    setRegister{s: Set}{c: IntegralConversion s t}: Register -> s -> M unit;

    loadByte: t -> M Int8;
    loadHalf: t -> M Int16;
    loadWord: t -> M Int32;
    loadDouble: t -> M Int64;

    storeByte: t -> Int8 -> M unit;
    storeHalf: t -> Int16 -> M unit;
    storeWord: t -> Int32 -> M unit;
    storeDouble: t -> Int64 -> M unit;

    getPC: M t;
    setPC: t -> M unit;

    step: M unit; (* updates PC *)

    raiseException: t -> t -> M unit;
  }.

End Riscv.
