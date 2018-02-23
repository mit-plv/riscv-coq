Require Import bbv.Word.
Require Import riscv.util.NameWithEq.

(* t will be instantiated with a signed type, u with an unsigned type.
   By default, all operations are on signed numbers. *)
Class Alu(t u: Set) := mkAlu {
  (* arithmetic operations: *)
  add: t -> t -> t;
  sub: t -> t -> t;
  mul: t -> t -> t;
  div: t -> t -> t;
  rem: t -> t -> t;

  (* comparison operators: *)
  signed_less_than: t -> t -> bool;
  unsigned_less_than: u -> u -> bool;

  (* logical operations: *)
  sll: t -> t -> t;
  srl: t -> t -> t;
  sra: t -> t -> t;
  xor: t -> t -> t;
  or: t -> t -> t;
  and: t -> t -> t;

  (* conversion operations: *)
  signed: u -> t;
  unsigned: t -> u;
}.

Notation "a <|> b" := (or a b) (at level 50, left associativity).
Notation "a <&> b" := (and a b) (at level 40, left associativity).
Notation "a + b" := (add a b) (at level 50, left associativity).
Notation "a - b" := (sub a b) (at level 50, left associativity).

Class IntegralConversion(t1 t2: Set) := mkIntegralConversion {
  fromIntegral: t1 -> t2
}.

Section Riscv.

  Context {Name: NameWithEq}. (* register name *)
  Notation Register := (@name Name).

  Class RiscvState(M: Type -> Type){t u: Set}{A: Alu t u} := mkRiscvState {
    getRegister: Register -> M t;
    setRegister{s: Set}{c: IntegralConversion s t}: Register -> s -> M unit;

    loadByte: t -> M (word 8);
    loadHalf: t -> M (word 16);
    loadWord: t -> M (word 32);
    loadDouble: t -> M (word 64);

    storeByte: t -> (word 8) -> M unit;
    storeHalf: t -> (word 16) -> M unit;
    storeWord: t -> (word 32) -> M unit;
    storeDouble: t -> (word 64) -> M unit;

    getPC: M t;
    setPC: t -> M unit;

    step: M unit; (* updates PC *)
  }.

End Riscv.
