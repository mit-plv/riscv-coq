From riscv Require Import Decode.
From riscv Require ExecuteI.
From riscv Require ExecuteI64.
From riscv Require ExecuteM.
From riscv Require ExecuteM64.
From riscv Require ExecuteCSR.
From riscv Require Import Monads.
Require Import riscv.Spec.Machine.
From riscv Require Import Utility.

(* Note: Filtering of unsupported instructions was already done in Decode, and they are
   turned into `InvalidInstruction i` *)
Definition execute {p} {t} `{(RiscvMachine p t)}(inst: Instruction): p unit :=
  match inst with
  | IInstruction i       => ExecuteI.execute i
  | MInstruction i       => ExecuteM.execute i
  | I64Instruction i     => ExecuteI64.execute i
  | M64Instruction i     => ExecuteM64.execute i
  | CSRInstruction i     => ExecuteCSR.execute i
  | InvalidInstruction i => raiseExceptionWithInfo (ZToReg 0) (ZToReg 2) (ZToReg i)
  (* Not supported by this spec: *)
  | AInstruction _ | FInstruction _ | A64Instruction _ | F64Instruction _ => raiseException (ZToReg 0) (ZToReg 2)
  end.
