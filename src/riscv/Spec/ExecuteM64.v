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

(* Converted imports: *)

Require Import Monads.
Require Spec.Decode.
Require Spec.Machine.
Require Import Utility.
Require Utility.Utility.

(* No type declarations to convert. *)

(* Converted value declarations: *)

Definition execute {p : Type -> Type} {t : Type} `{Spec.Machine.RiscvMachine p
                                                                             t}
   : Spec.Decode.InstructionM64 -> p unit :=
  fun arg_0__ =>
    match arg_0__ with
    | Spec.Decode.Mulw rd rs1 rs2 =>
        Bind (Spec.Machine.getRegister rs1) (fun x =>
                Bind (Spec.Machine.getRegister rs2) (fun y =>
                        Spec.Machine.setRegister rd (Utility.Utility.s32 (x * y))))
    | Spec.Decode.Divw rd rs1 rs2 =>
        Bind (Spec.Machine.getRegister rs1) (fun x =>
                Bind (Spec.Machine.getRegister rs2) (fun y =>
                        let q :=
                          if andb (reg_eqb x Utility.Utility.minSigned) (reg_eqb y (negate (ZToReg
                                                                                            1))) : bool
                          then x else
                          if reg_eqb y (ZToReg 0) : bool then negate (ZToReg 1) else
                          div x y in
                        Spec.Machine.setRegister rd (Utility.Utility.s32 q)))
    | Spec.Decode.Divuw rd rs1 rs2 =>
        Bind (Spec.Machine.getRegister rs1) (fun x =>
                Bind (Spec.Machine.getRegister rs2) (fun y =>
                        let q :=
                          if reg_eqb y (ZToReg 0) : bool then Utility.Utility.maxUnsigned else
                          Utility.Utility.divu x y in
                        Spec.Machine.setRegister rd (Utility.Utility.s32 q)))
    | Spec.Decode.Remw rd rs1 rs2 =>
        Bind (Spec.Machine.getRegister rs1) (fun x =>
                Bind (Spec.Machine.getRegister rs2) (fun y =>
                        let r :=
                          if andb (reg_eqb x Utility.Utility.minSigned) (reg_eqb y (negate (ZToReg
                                                                                            1))) : bool
                          then ZToReg 0 else
                          if reg_eqb y (ZToReg 0) : bool then x else
                          rem x y in
                        Spec.Machine.setRegister rd (Utility.Utility.s32 r)))
    | Spec.Decode.Remuw rd rs1 rs2 =>
        Bind (Spec.Machine.getRegister rs1) (fun x =>
                Bind (Spec.Machine.getRegister rs2) (fun y =>
                        let r := if reg_eqb y (ZToReg 0) : bool then x else Utility.Utility.remu x y in
                        Spec.Machine.setRegister rd (Utility.Utility.s32 r)))
    | inst => Return tt
    end.

(* External variables:
     Bind Return Type ZToReg andb bool div negate op_zt__ reg_eqb rem tt unit
     Spec.Decode.Divuw Spec.Decode.Divw Spec.Decode.InstructionM64 Spec.Decode.Mulw
     Spec.Decode.Remuw Spec.Decode.Remw Spec.Machine.RiscvMachine
     Spec.Machine.getRegister Spec.Machine.setRegister Utility.Utility.divu
     Utility.Utility.maxUnsigned Utility.Utility.minSigned Utility.Utility.remu
     Utility.Utility.s32
*)
