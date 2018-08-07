
Require Import Decode.
Require ExecuteI.
Require ExecuteI64.
Require ExecuteM.
Require ExecuteM64.
Require Import Monads.
Require Import Program.
Require Import Utility.

(* No type declarations to convert. *)
(* Converted value declarations: *)

(* Note: Filtering of unsupported instructions was already done in Decode.
   Note: We don't support CSR instructions yet. *)
Definition execute {p} {t} `{(RiscvState p t)}(inst: Instruction): p unit :=
  match inst with
  | IInstruction i     => ExecuteI.execute i
  | MInstruction i     => ExecuteM.execute i
  | I64Instruction i   => ExecuteI64.execute i
  | M64Instruction i   => ExecuteM64.execute i
  | _                  => raiseException (ZToReg 0) (ZToReg 2)
  end.
