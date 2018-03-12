Require Import riscv.util.NameWithEq.
Require Import riscv.util.Monads.
Require Import riscv.Utility.
Require Import Coq.ZArith.BinInt.
Require Import bbv.Word.

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

    (* TODO support all get/setCSRField, this one is just for the exception handler address *)
    getCSRField_MTVecBase: M MachineInt;

    step: M unit; (* updates PC *)

    endCycle: forall {A}, M A;
  }.


  Definition raiseException{A: Type}{t: Set}{MW: MachineWidth t}{M: Type -> Type}
    {MM: Monad M}{RVS: RiscvState M}
    (isInterrupt: t)(exceptionCode: t): M A :=
    pc <- getPC;
    addr <- getCSRField_MTVecBase;
    setPC (fromImm (addr * 4)%Z);;
    endCycle.

End Riscv.
