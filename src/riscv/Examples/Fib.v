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
Require Import riscv.Utility.Words32Naive.
Require Import riscv.Utility.DefaultMemImpl32.
Require Import coqutil.Map.Z_keyed_SortedListMap.

Require coqutil.Map.SortedList.

Definition fib6_riscv: list MachineInt := [ (* TODO should be "word32", not MachineInt *)
  0x00600993;         (* li s3,6 *)
  0x00000a13;         (* li s4,0 *)
  0x00100913;         (* li s2,1 *)
  0x00000493;         (* li s1,0 *)
  0x0140006f;         (* j 101e0 <main+0x44> *)
  0x012a0ab3;         (* add s5,s4,s2 *)
  0x00090a13;         (* mv s4,s2 *)
  0x000a8913;         (* mv s2,s5 *)
  0x00148493;         (* addi s1,s1,1 *)
  0xff34c8e3          (* blt s1,s3,101d0 <main+0x34> *)
].

(*
Notation x0 := (WO~0~0~0~0~0)%word.
Notation s1 := (WO~0~1~0~0~1)%word.
Notation s2 := (WO~1~0~0~1~0)%word.
Notation s3 := (WO~1~0~0~1~1)%word.
Notation s4 := (WO~1~0~1~0~0)%word.
Notation s5 := (WO~1~0~1~0~1)%word.
*)

Goal False.
  set (l := List.map (decode RV32IM) fib6_riscv).
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
  | S fuel' => match Run.run1 RV32IM s with
               | (Some _, s') => run fuel' s'
               | (None, s') => (false, s')
               end
  end.

Definition fib6_final(fuel: nat): RiscvMachine :=
  match run fuel (initialRiscvMachine fib6_riscv) with
  | (answer, state) => state
  end.

Definition fib6_res(fuel: nat): word32 :=
  match map.get (fib6_final fuel).(getRegs) 18 with
  | Some v => v
  | None => word.of_Z 0
  end.

Definition fib6_trace(fuel: nat): list LogItem :=
  (fib6_final fuel).(getLog).

(* only uncomment this if you're sure there are no admits in the computational parts,
   otherwise this will eat all your memory *)

Example trace_result := Eval vm_compute in (fib6_trace 50).

Lemma fib6_res_is_13_by_running_it: exists fuel, fib6_res fuel = word.of_Z 13.
  exists 50%nat.
  reflexivity.
Qed.
