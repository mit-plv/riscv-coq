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
Require Import Utility.
Local Open Scope alu_scope.

(* Converted imports: *)

Require Decode.
Require Import Monads.
Require Import Program.
Require Import Utility.

(* No type declarations to convert. *)
(* Converted value declarations: *)

Definition execute {p} {t} `{(RiscvState p t)}
   : Decode.InstructionM64 -> p unit :=
  fun arg_0__ =>
    match arg_0__ with
    | Decode.Mulw rd rs1 rs2 =>
        Bind (getRegister rs1) (fun x =>
                Bind (getRegister rs2) (fun y => setRegister rd (s32 (x * y))))
    | Decode.Divw rd rs1 rs2 =>
        Bind (getRegister rs1) (fun x =>
                Bind (getRegister rs2) (fun y =>
                        let q :=
                          if andb (reg_eqb x minSigned) (reg_eqb y (negate (ZToReg 1))) : bool then x else
                          if reg_eqb y (ZToReg 0) : bool then negate (ZToReg 1) else
                          div x y in
                        setRegister rd (s32 q)))
    | Decode.Divuw rd rs1 rs2 =>
        Bind (getRegister rs1) (fun x =>
                Bind (getRegister rs2) (fun y =>
                        let q := if reg_eqb y (ZToReg 0) : bool then maxUnsigned else divu x y in
                        setRegister rd (s32 q)))
    | Decode.Remw rd rs1 rs2 =>
        Bind (getRegister rs1) (fun x =>
                Bind (getRegister rs2) (fun y =>
                        let r :=
                          if andb (reg_eqb x minSigned) (reg_eqb y (negate (ZToReg 1))) : bool
                          then ZToReg 0 else
                          if reg_eqb y (ZToReg 0) : bool then x else
                          rem x y in
                        setRegister rd (s32 r)))
    | Decode.Remuw rd rs1 rs2 =>
        Bind (getRegister rs1) (fun x =>
                Bind (getRegister rs2) (fun y =>
                        let r := if reg_eqb y (ZToReg 0) : bool then x else remu x y in
                        setRegister rd (s32 r)))
    | inst => Return tt
    end.

(* External variables:
     Bind Return RiscvState ZToReg andb bool div divu getRegister maxUnsigned
     minSigned negate op_zt__ reg_eqb rem remu s32 setRegister tt unit Decode.Divuw
     Decode.Divw Decode.InstructionM64 Decode.Mulw Decode.Remuw Decode.Remw
*)
