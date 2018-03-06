Require Import riscv.util.NameWithEq.
Require Import riscv.Utility.
Require Import Coq.ZArith.BinInt.
Require Import bbv.Word.

Notation "a <|> b" := (or a b)  (at level 50, left associativity) : alu_scope.
Notation "a <&> b" := (and a b) (at level 40, left associativity) : alu_scope.
Notation "a + b"   := (add a b) (at level 50, left associativity) : alu_scope.
Notation "a - b"   := (sub a b) (at level 50, left associativity) : alu_scope.

Notation "a /= b" := (negb (signed_eqb a b))        (at level 70, no associativity) : alu_scope.
Notation "a == b" := (signed_eqb a b)               (at level 70, no associativity) : alu_scope.
Notation "a < b"  := (signed_less_than a b)         (at level 70, no associativity) : alu_scope.
Notation "a >= b" := (negb (signed_less_than a b))  (at level 70, no associativity) : alu_scope.

Section Constants.
  Context {t: Set}.
  Context {MW: MachineWidth t}.

  Local Open Scope alu_scope.

  Definition two: t := one + one.

  Definition four: t := two + two.

End Constants.

Section Riscv.

  Context {Name: NameWithEq}. (* register name *)
  Notation Register := (@name Name).

  Class RiscvState(M: Type -> Type){t: Set}{MW: MachineWidth t} := mkRiscvState {
    getRegister: Register -> M t;
    setRegister: Register -> t -> M unit;

    loadByte: t -> M (word 8);
    loadHalf: t -> M (word 16);
    loadWord: t -> M (word 32);
    loadDouble: t -> M (word 64);

    storeByte: t -> word 8 -> M unit;
    storeHalf: t -> word 16 -> M unit;
    storeWord: t -> word 32 -> M unit;
    storeDouble: t -> word 64 -> M unit;

    getPC: M t;
    setPC: t -> M unit;

    step: M unit; (* updates PC *)

    raiseException: t -> t -> M unit;
  }.

End Riscv.
