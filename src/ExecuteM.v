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
   : Decode.InstructionM -> p unit :=
  fun arg_0__ =>
    match arg_0__ with
    | Decode.Mul rd rs1 rs2 =>
        Bind (getRegister rs1) (fun x =>
                Bind (getRegister rs2) (fun y => setRegister rd (x * y)))
    | Decode.Mulh rd rs1 rs2 =>
        Bind (getRegister rs1) (fun x =>
                Bind (getRegister rs2) (fun y =>
                        setRegister rd (highBits (regToZ_signed x * regToZ_signed y) : t)))
    | Decode.Mulhsu rd rs1 rs2 =>
        Bind (getRegister rs1) (fun x =>
                Bind (getRegister rs2) (fun y =>
                        setRegister rd (highBits (regToZ_signed x * regToZ_unsigned y) : t)))
    | Decode.Mulhu rd rs1 rs2 =>
        Bind (getRegister rs1) (fun x =>
                Bind (getRegister rs2) (fun y =>
                        setRegister rd (highBits (regToZ_unsigned x * regToZ_unsigned y) : t)))
    | Decode.Div rd rs1 rs2 =>
        Bind (getRegister rs1) (fun x =>
                Bind (getRegister rs2) (fun y =>
                        let q :=
                          if andb (signed_eqb x minSigned) (signed_eqb y (negate one)) : bool then x else
                          if signed_eqb y zero : bool then negate one else
                          div x y in
                        setRegister rd q))
    | Decode.Divu rd rs1 rs2 =>
        Bind (getRegister rs1) (fun x =>
                Bind (getRegister rs2) (fun y =>
                        let q := if signed_eqb y zero : bool then maxUnsigned else divu x y in
                        setRegister rd q))
    | Decode.Rem rd rs1 rs2 =>
        Bind (getRegister rs1) (fun x =>
                Bind (getRegister rs2) (fun y =>
                        let r :=
                          if andb (signed_eqb x minSigned) (signed_eqb y (negate one)) : bool
                          then zero else
                          if signed_eqb y zero : bool then x else
                          rem x y in
                        setRegister rd r))
    | Decode.Remu rd rs1 rs2 =>
        Bind (getRegister rs1) (fun x =>
                Bind (getRegister rs2) (fun y =>
                        let r := if signed_eqb y zero : bool then x else remu x y in setRegister rd r))
    | inst => Return tt
    end.

(* External variables:
     Bind Return RiscvState andb bool div divu getRegister highBits maxUnsigned
     minSigned negate one op_zt__ regToZ_signed regToZ_unsigned rem remu setRegister
     signed_eqb tt unit zero Decode.Div Decode.Divu Decode.InstructionM Decode.Mul
     Decode.Mulh Decode.Mulhsu Decode.Mulhu Decode.Rem Decode.Remu
*)
