Require Import Coq.ZArith.ZArith.
Require Import riscv.util.Monads.
Require Import riscv.Utility.
Require Import riscv.Decode.


Inductive AccessType: Set := Instr | Load | Store.

Class RiscvProgram{M}{t}`{Monad M}`{MachineWidth t} := mkRiscvProgram {
  getRegister: Register -> M t;
  setRegister: Register -> t -> M unit;

  loadByte: t -> M w8;
  loadHalf: t -> M w16;
  loadWord: t -> M w32;
  loadDouble: t -> M w64;

  storeByte: t -> w8 -> M unit;
  storeHalf: t -> w16 -> M unit;
  storeWord: t -> w32 -> M unit;
  storeDouble: t -> w64 -> M unit;

  getPC: M t;
  setPC: t -> M unit;

  step: M unit; (* updates PC *)

  (* Returns false on out of range addresses, on MMIO addresses, device addresses, etc
  isPhysicalMemAddr: t -> M bool;
     not needed at the moment because we expose state record *)

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
  Context {t: Type}.

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
