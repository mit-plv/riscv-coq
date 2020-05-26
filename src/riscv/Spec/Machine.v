(*tag:importboilerplate*)
Require Import Coq.ZArith.ZArith.
Require Import riscv.Utility.Monads.
Require Import riscv.Utility.Utility.
Require Import riscv.Spec.Decode.

(*tag:spec*)
Inductive AccessType: Type := Instr | Load | Store.
Inductive SourceType: Type := VirtualMemory | Fetch | Execute.

Class RiscvProgram{M}{t}`{Monad M}`{MachineWidth t} := mkRiscvProgram {
  getRegister: Register -> M t;
  setRegister: Register -> t -> M unit;

  loadByte   : SourceType -> t -> M w8;
  loadHalf   : SourceType -> t -> M w16;
  loadWord   : SourceType -> t -> M w32;
  loadDouble : SourceType -> t -> M w64;

  storeByte   : SourceType -> t -> w8 -> M unit;
  storeHalf   : SourceType -> t -> w16 -> M unit;
  storeWord   : SourceType -> t -> w32 -> M unit;
  storeDouble : SourceType -> t -> w64 -> M unit;

  makeReservation  : t -> M unit;
  clearReservation : t -> M unit;
  checkReservation : t -> M bool;

  getPC: M t;
  setPC: t -> M unit;

  step: M unit; (* updates PC *)

  (* Returns false on out of range addresses, on MMIO addresses, device addresses, etc
  isPhysicalMemAddr: t -> M bool;
     not needed at the moment because we expose state record *)

  raiseExceptionWithInfo{A: Type}(isInterrupt: t)(exceptionCode: t)(info: t): M A;
}.


Class RiscvMachine`{MP: RiscvProgram} := mkRiscvMachine {
  (* checks that addr is aligned, and translates the (possibly virtual) addr to a physical
     address, raising an exception if the address is invalid *)
  translate(accessType: AccessType)(alignment: t)(addr: t): M t;
}.

(*tag:unrelated*)
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

  Definition raiseException{A: Type}{MP: RiscvProgram}
             (isInterrupt: t)(exceptionCode: t): M A :=
    raiseExceptionWithInfo isInterrupt exceptionCode (ZToReg 0).

  (* in a system with virtual memory, this would also do the translation, but in our
     case, we only verify the alignment *)
  Definition translate_with_alignment_check{MP: RiscvProgram}
    (accessType: AccessType)(alignment: t)(addr: t): M t :=
    if remu addr alignment /= ZToReg 0
    then raiseException (ZToReg 0) (ZToReg 4)
    else Return addr.

  (*tag:spec*)
  Instance DefaultRiscvState{MP: RiscvProgram}: RiscvMachine := {|
    (*tag:doc*)
    (* riscv does allow misaligned memory access (but might emulate them in software),
       so for the compiler-facing side, we don't do alignment checks, but might add
       another riscv machine layer below to emulate turn misaligned accesses into two
       aligned accesses *)
    (*tag:spec*)
    translate accessType alignment := @Return M MM t;
  |}.

End Riscv.

Definition Register0: Register := 0%Z.

(*tag:administrivia*)
Arguments RiscvProgram: clear implicits.
Arguments RiscvProgram (M) (t) {_} {_}.
Arguments RiscvMachine: clear implicits.
Arguments RiscvMachine (M) (t) {_} {_} {_}.

Existing Instance DefaultRiscvState.
