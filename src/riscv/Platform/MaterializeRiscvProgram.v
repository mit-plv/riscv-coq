Require Import riscv.Utility.Monads.
Require Import riscv.Utility.FreeMonad.
Require Import riscv.Spec.Decode.
Require Import riscv.Spec.Machine.
Require Import riscv.Utility.MkMachineWidth.
Require Import riscv.Utility.Utility.

Section Riscv.
  Import free.
  Context {W: Words}.

  Variant riscv_primitive :=
  | getRegister (_ : Register)
  | setRegister (_ : Register) (_ : word)
  | loadByte (_ : SourceType) (_ : word)
  | loadHalf (_ : SourceType) (_ : word)
  | loadWord (_ : SourceType) (_ : word)
  | loadDouble (_ : SourceType) (_ : word)
  | storeByte (_ : SourceType) (_ : word) (_ : w8)
  | storeHalf (_ : SourceType) (_ : word) (_ : w16)
  | storeWord (_ : SourceType) (_ : word) (_ : w32)
  | storeDouble (_ : SourceType) (_ : word) (_ : w64)
  | makeReservation (_ : word)
  | clearReservation (_ : word)
  | checkReservation (_ : word)
  | getCSRField (_ : CSRField.CSRField)
  | setCSRField (_ : CSRField.CSRField) (_ : MachineInt)
  | getPrivMode
  | setPrivMode (_ : PrivMode)
  | getPC
  | setPC (_ : word)
  | endCycleNormal
  | endCycleEarly (_ : Type)
  .

  Definition primitive_result (action : riscv_primitive) : Type :=
    match action with
    | getRegister _ => word
    | setRegister _ _ => unit
    | loadByte _ _ => w8
    | loadHalf _ _ => w16
    | loadWord _ _ => w32
    | loadDouble _ _ => w64
    | storeByte _ _ _ | storeHalf _ _ _ | storeWord _ _ _ | storeDouble _ _ _ => unit
    | makeReservation _ | clearReservation _ => unit
    | checkReservation _ => bool
    | getCSRField _ => MachineInt
    | setCSRField _ _ => unit
    | getPrivMode => PrivMode
    | setPrivMode _ => unit
    | getPC => word
    | setPC _ => unit
    | endCycleNormal => unit
    | endCycleEarly T => T
    end.

  Global Instance Materialize: RiscvProgram (free riscv_primitive primitive_result) word := {|
    Machine.getRegister a := act (getRegister a) ret;
    Machine.setRegister a b := act (setRegister a b) ret;
    Machine.loadByte a b := act (loadByte a b) ret;
    Machine.loadHalf a b := act (loadHalf a b) ret;
    Machine.loadWord a b := act (loadWord a b) ret;
    Machine.loadDouble a b := act (loadDouble a b) ret;
    Machine.storeByte a b c := act (storeByte a b c) ret;
    Machine.storeHalf a b c := act (storeHalf a b c) ret;
    Machine.storeWord a b c := act (storeWord a b c) ret;
    Machine.storeDouble a b c := act (storeDouble a b c) ret;
    Machine.makeReservation a := act (makeReservation a) ret;
    Machine.clearReservation a := act (clearReservation a) ret;
    Machine.checkReservation a := act (checkReservation a) ret;
    Machine.getCSRField f := act (getCSRField f) ret;
    Machine.setCSRField f v := act (setCSRField f v) ret;
    Machine.getPrivMode := act getPrivMode ret;
    Machine.setPrivMode m := act (setPrivMode m) ret;
    Machine.getPC := act getPC ret;
    Machine.setPC a := act (setPC a) ret;
    Machine.endCycleNormal := act endCycleNormal ret;
    Machine.endCycleEarly A := act (endCycleEarly A) ret;
  |}.

End Riscv.
