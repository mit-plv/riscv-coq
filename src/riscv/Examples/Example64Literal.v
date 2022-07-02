Require Import Coq.Lists.List.
Require Import coqutil.Z.Lia.
Import ListNotations.
Require Import coqutil.Word.Naive.
Require Import coqutil.Word.Properties.
Require Import riscv.Spec.Machine.
Require Import riscv.Spec.Decode.
Require Import Coq.ZArith.BinInt. Local Open Scope Z_scope.
Require Import riscv.Utility.Utility.
Require Import riscv.Platform.Memory.
Require Import riscv.Platform.Minimal.
Require Import riscv.Platform.MinimalLogging.
Require Import riscv.Platform.Run.
Require Import riscv.Utility.Monads.
Require Import riscv.Utility.MkMachineWidth.
Require Import coqutil.Map.Interface.
Require Import riscv.Utility.Words64Naive.
Require Import riscv.Utility.DefaultMemImpl64.
Require Import coqutil.Map.Z_keyed_SortedListMap.
Require coqutil.Map.SortedList.

#[global] Existing Instance DefaultRiscvState.


Definition foo7prog: list MachineInt := [
  0x400017b7; (* lui    a5,0x40001 *)
  0xfff78793  (* addi   a5,a5,-1 *)
].
Definition foo7val: Z := 0x40000fff.

Definition literaltest_riscv := foo7prog.
Definition expected_res      := foo7val.

Goal False.
  set (l := List.map (decode RV64IM) literaltest_riscv).
  cbv in l.
  (* decoder seems to work :) *)
Abort.

(* This example uses the memory only as instruction memory
   TODO make an example which uses memory to store data *)
Definition zeroedRiscvMachine: RiscvMachine := {|
  getRegs := map.empty;
  getPc := ZToReg 0;
  getNextPc := ZToReg 4;
  getMem := map.empty;
  getXAddrs := nil;
  getLog := nil;
|}.

Definition initialRiscvMachine(imem: list MachineInt): RiscvMachine :=
  putProgram imem (ZToReg 0) zeroedRiscvMachine.

(* success flag * final state *)
Fixpoint run(fuel: nat)(s: RiscvMachine): bool * RiscvMachine :=
  match fuel with
  | O => (true, s)
  | S fuel' => match Run.run1 RV64IM s with
               | (Some _, s') => run fuel' s'
               | (None, s') => (false, s')
               end
  end.

Definition literaltest_final(fuel: nat): RiscvMachine :=
  match run fuel (initialRiscvMachine literaltest_riscv) with
  | (answer, state) => state
  end.

Definition literaltest_res(fuel: nat): word64 :=
  match map.get (literaltest_final fuel).(getRegs) 15 with
  | Some v => v
  | None => word.of_Z 0
  end.

Eval vm_compute in (literaltest_res 50).

Lemma literaltest_res_run_test: exists fuel, literaltest_res fuel = word.of_Z expected_res.
  exists 50%nat.
  reflexivity.
Qed.
