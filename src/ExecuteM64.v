(* Default settings (from HsToCoq.Coq.Preamble) *)

Generalizable All Variables.

Unset Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Coq.Program.Tactics.
Require Coq.Program.Wf.

(* Preamble *)

Require Import Utility.
Local Open Scope alu_scope.

(* Converted imports: *)

Require Decode.
Require GHC.Num.
Require Import GHC.Real.
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
                Bind (getRegister rs2) (fun y => setRegister rd (s32 (mul x y))))
    | Decode.Divw rd rs1 rs2 =>
        Bind (getRegister rs1) (fun x =>
                Bind (getRegister rs2) (fun y =>
                        let q :=
                          if andb (signed_eqb x minSigned) (signed_eqb y (GHC.Num.negate one)) : bool
                          then x else
                          if signed_eqb y zero : bool then GHC.Num.negate one else
                          quot x y in
                        setRegister rd (s32 q)))
    | Decode.Divuw rd rs1 rs2 =>
        Bind (getRegister rs1) (fun x =>
                Bind (getRegister rs2) (fun y =>
                        let q := if signed_eqb y zero : bool then maxUnsigned else divu x y in
                        setRegister rd (s32 q)))
    | Decode.Remw rd rs1 rs2 =>
        Bind (getRegister rs1) (fun x =>
                Bind (getRegister rs2) (fun y =>
                        let r :=
                          if andb (signed_eqb x minSigned) (signed_eqb y (GHC.Num.negate one)) : bool
                          then zero else
                          if signed_eqb y zero : bool then x else
                          rem x y in
                        setRegister rd (s32 r)))
    | Decode.Remuw rd rs1 rs2 =>
        Bind (getRegister rs1) (fun x =>
                Bind (getRegister rs2) (fun y =>
                        let r := if signed_eqb y zero : bool then x else remu x y in
                        setRegister rd (s32 r)))
    | inst => Return tt
    end.

(* Unbound variables:
     Bind Return RiscvState andb bool divu getRegister maxUnsigned minSigned mul one
     quot rem remu s32 setRegister signed_eqb tt unit zero Decode.Divuw Decode.Divw
     Decode.InstructionM64 Decode.Mulw Decode.Remuw Decode.Remw GHC.Num.negate
*)
