(* Default settings (from HsToCoq.Coq.Preamble) *)

Generalizable All Variables.

Unset Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Coq.Program.Tactics.
Require Coq.Program.Wf.

(* Preamble *)

Require Import Coq.ZArith.BinInt.
Local Open Scope Z.
Require Import riscv.Utility.Utility.
Local Open Scope alu_scope.

(* No imports to convert. *)

(* Converted type declarations: *)

Inductive FieldType : Type :=
  | RO : FieldType
  | RW : FieldType
  | WLRL : FieldType
  | WARL : FieldType.

Inductive CSRField : Type :=
  | MXL : CSRField
  | Extensions : CSRField
  | SXL : CSRField
  | UXL : CSRField
  | TSR : CSRField
  | TW : CSRField
  | TVM : CSRField
  | MXR : CSRField
  | SUM : CSRField
  | MPRV : CSRField
  | XS : CSRField
  | FS : CSRField
  | MPP : CSRField
  | SPP : CSRField
  | MPIE : CSRField
  | SPIE : CSRField
  | UPIE : CSRField
  | MIE : CSRField
  | SIE : CSRField
  | UIE : CSRField
  | SD : CSRField
  | MTVecBase : CSRField
  | MTVecMode : CSRField
  | MEDeleg : CSRField
  | MIDeleg : CSRField
  | MEIP : CSRField
  | SEIP : CSRField
  | UEIP : CSRField
  | MTIP : CSRField
  | STIP : CSRField
  | UTIP : CSRField
  | MSIP : CSRField
  | SSIP : CSRField
  | USIP : CSRField
  | MEIE : CSRField
  | SEIE : CSRField
  | UEIE : CSRField
  | MTIE : CSRField
  | STIE : CSRField
  | UTIE : CSRField
  | MSIE : CSRField
  | SSIE : CSRField
  | USIE : CSRField
  | MCycle : CSRField
  | MInstRet : CSRField
  | MHPM : CSRField
  | MIR : CSRField
  | MTM : CSRField
  | MCY : CSRField
  | MScratch : CSRField
  | MEPC : CSRField
  | MCauseInterrupt : CSRField
  | MCauseCode : CSRField
  | MTVal : CSRField
  | STVecBase : CSRField
  | STVecMode : CSRField
  | SHPM : CSRField
  | SIR : CSRField
  | STM : CSRField
  | SCY : CSRField
  | SScratch : CSRField
  | SEPC : CSRField
  | SCauseInterrupt : CSRField
  | SCauseCode : CSRField
  | STVal : CSRField
  | MODE : CSRField
  | ASID : CSRField
  | PPN : CSRField
  | FFlags : CSRField
  | FRM : CSRField.

(* Converted value declarations: *)

(* Skipping instance `Spec.CSRField.Ord__CSRField' of class `GHC.Base.Ord' *)

(* Skipping instance `Spec.CSRField.Ix__CSRField' of class `GHC.Arr.Ix' *)

(* Skipping instance `Spec.CSRField.Eq___CSRField' of class `GHC.Base.Eq_' *)

(* Skipping instance `Spec.CSRField.Show__CSRField' of class `GHC.Show.Show' *)

(* Skipping instance `Spec.CSRField.Show__FieldType' of class `GHC.Show.Show' *)

(* Skipping instance `Spec.CSRField.Eq___FieldType' of class `GHC.Base.Eq_' *)

Definition fieldType : CSRField -> FieldType :=
  fun arg_0__ =>
    match arg_0__ with
    | MXL => WARL
    | Extensions => WARL
    | XS => RO
    | SD => RO
    | MTVecBase => WARL
    | MTVecMode => WARL
    | MEDeleg => WARL
    | MIDeleg => WARL
    | MHPM => WARL
    | MIR => WARL
    | MTM => WARL
    | MCY => WARL
    | MEPC => WARL
    | MCauseCode => WLRL
    | MTVal => WARL
    | STVecBase => WARL
    | STVecMode => WARL
    | SEPC => WARL
    | SCauseCode => WLRL
    | STVal => WARL
    | MODE => WARL
    | ASID => WARL
    | PPN => WARL
    | _ => RW
    end.
