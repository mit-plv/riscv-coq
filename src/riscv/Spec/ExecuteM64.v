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
                        let b := Utility.Utility.s32 y in
                        let a := Utility.Utility.s32 x in
                        let q :=
                          if andb (reg_eqb a Utility.Utility.minSigned32) (reg_eqb b (negate (ZToReg
                                                                                              1))) : bool
                          then a else
                          if reg_eqb b (ZToReg 0) : bool then negate (ZToReg 1) else
                          div a b in
                        Spec.Machine.setRegister rd (Utility.Utility.s32 q)))
    | Spec.Decode.Divuw rd rs1 rs2 =>
        Bind (Spec.Machine.getRegister rs1) (fun x =>
                Bind (Spec.Machine.getRegister rs2) (fun y =>
                        let b := Utility.Utility.u32 y in
                        let a := Utility.Utility.u32 x in
                        let q :=
                          if reg_eqb b (ZToReg 0) : bool then Utility.Utility.maxUnsigned else
                          Utility.Utility.divu a b in
                        Spec.Machine.setRegister rd (Utility.Utility.s32 q)))
    | Spec.Decode.Remw rd rs1 rs2 =>
        Bind (Spec.Machine.getRegister rs1) (fun x =>
                Bind (Spec.Machine.getRegister rs2) (fun y =>
                        let b := Utility.Utility.s32 y in
                        let a := Utility.Utility.s32 x in
                        let r :=
                          if andb (reg_eqb a Utility.Utility.minSigned32) (reg_eqb b (negate (ZToReg
                                                                                              1))) : bool
                          then ZToReg 0 else
                          if reg_eqb b (ZToReg 0) : bool then a else
                          rem a b in
                        Spec.Machine.setRegister rd (Utility.Utility.s32 r)))
    | Spec.Decode.Remuw rd rs1 rs2 =>
        Bind (Spec.Machine.getRegister rs1) (fun x =>
                Bind (Spec.Machine.getRegister rs2) (fun y =>
                        let b := Utility.Utility.u32 y in
                        let a := Utility.Utility.u32 x in
                        let r := if reg_eqb b (ZToReg 0) : bool then a else Utility.Utility.remu a b in
                        Spec.Machine.setRegister rd (Utility.Utility.s32 r)))
    | inst => Return tt
    end.

(* External variables:
     Bind Return Type ZToReg andb bool div negate op_zt__ reg_eqb rem tt unit
     Spec.Decode.Divuw Spec.Decode.Divw Spec.Decode.InstructionM64 Spec.Decode.Mulw
     Spec.Decode.Remuw Spec.Decode.Remw Spec.Machine.RiscvMachine
     Spec.Machine.getRegister Spec.Machine.setRegister Utility.Utility.divu
     Utility.Utility.maxUnsigned Utility.Utility.minSigned32 Utility.Utility.remu
     Utility.Utility.s32 Utility.Utility.u32
*)
