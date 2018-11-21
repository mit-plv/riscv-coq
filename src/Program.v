Require Import Coq.ZArith.ZArith.
Require Import riscv.util.Monads.
Require Import riscv.util.Word.
Require Import riscv.Utility.
Require Import riscv.Decode.


Inductive AccessType: Set := Instr | Load | Store.

Class RiscvProgram{M}{t}`{Monad M}`{MachineWidth t} := mkRiscvProgram {
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

  raiseException{A: Type}(isInterrupt: t)(exceptionCode: t): M A;
}.


Class RiscvState`{MP: RiscvProgram} := mkRiscvState {
  (* checks that addr is aligned, and translates the (possibly virtual) addr to a physical
     address, raising an exception if the address is invalid *)
  translate(accessType: AccessType)(alignment: t)(addr: t): M t;
}.


Section Riscv.
  (* monad (will be instantiated with some kind of state monad) *)
  Context {M: Type -> Type}.
  Context {MM: Monad M}.

  (* type of register values *)
  Context {t: Set}.

  (* provides operations on t *)
  Context {MW: MachineWidth t}.

  Local Open Scope alu_scope.
  Local Open Scope Z_scope.

  (* in a system with virtual memory, this would also do the translation, but in our
     case, we only verify the alignment *)
  Definition default_translate{MP: RiscvProgram}
    (accessType: AccessType)(alignment: t)(addr: t): M t :=
    if remu addr alignment /= ZToReg 0
    then raiseException (ZToReg 0) (ZToReg 4)
    else Return addr.

  Instance DefaultRiscvState{MP: RiscvProgram}: RiscvState := {|
    translate := default_translate;
  |}.

End Riscv.

Definition Register0: Register := 0%Z.

Arguments RiscvProgram: clear implicits.
Arguments RiscvProgram (M) (t) {_} {_}.
Arguments RiscvState: clear implicits.
Arguments RiscvState (M) (t) {_} {_} {_}.
