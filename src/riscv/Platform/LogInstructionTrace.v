Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import riscv.Utility.Monads. Import StateAbortFailOperations.
Require Import riscv.Utility.MonadNotations.
Require Import riscv.Spec.Decode.
Require Import riscv.Spec.Machine.
Require Import riscv.Utility.Utility.
Require Import riscv.Spec.Primitives.
Require Import riscv.Utility.ExtensibleRecords.
Require Import coqutil.Z.Lia.
Require Import coqutil.Map.Interface.

Local Open Scope Z_scope.
Local Open Scope bool_scope.
Import ListNotations.

Definition pc: nat := 1.
Definition mem: nat := 3.
Definition exectrace: nat := 8.

Definition ExecTrace: Type := list (Z * Instruction). (* pc and instruction *)

Section Riscv.
  Context {width: Z} {BW: Bitwidth width} {word: word width} {word_ok: word.ok word}.
  Context {Mem: map.map word byte}.
  Context (UnknownFields: natmap Type).

  Definition Fields: natmap Type := natmap.putmany UnknownFields [
    (pc, word: Type);
    (mem, Mem: Type);
    (exectrace, ExecTrace)
   ].

  Definition State: Type := hnatmap Fields.

  Import HnatmapNotations. Open Scope hnatmap_scope.

  Local Notation get := (@StateAbortFailOperations.get State). (* to improve type inference *)

  Global Instance AddExecTrace(RVP: RiscvProgram (StateAbortFail State) word):
    RiscvProgram (StateAbortFail State) word := {
    getRegister := getRegister;
    setRegister := setRegister;
    getPC := getPC;
    setPC := setPC;
    loadByte := loadByte;
    loadHalf := loadHalf;
    loadWord kind addr :=
      v <- loadWord kind addr;
      mach <- get;
      let i := match Memory.loadWord mach[mem] addr with
               | Some i => LittleEndian.combine 4 i
               | None => -1
               end in
      let i' := match kind with
                | Fetch => decode RV64IMAF i
                | _ => InvalidInstruction i
                end in
      put mach[exectrace := (word.unsigned addr, i') :: mach[exectrace]];;
      Return v;
    loadDouble := loadDouble;
    storeByte := storeByte;
    storeHalf := storeHalf;
    storeWord := storeWord;
    storeDouble := storeDouble;
    makeReservation := makeReservation;
    clearReservation := clearReservation;
    checkReservation := checkReservation;
    getCSRField := getCSRField;
    setCSRField := setCSRField;
    getPrivMode := getPrivMode;
    setPrivMode := setPrivMode;
    fence := fence;
    endCycleNormal := endCycleNormal;
    endCycleEarly{A} := @endCycleEarly _ _ _ _ _ A;
  }.

End Riscv.
