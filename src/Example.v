Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Import ListNotations.
Require Import coqutil.Word.Naive.
Require Import coqutil.Word.Properties.
Require Import riscv.Program.
Require Import riscv.Decode.
Require Import riscv.util.BitWidth32.
Require Import bbv.HexNotationZ.
Require Import Coq.ZArith.BinInt.
Require Import riscv.Utility.
Require Import riscv.Memory.
Require Import riscv.Minimal.
Require Import riscv.MinimalLogging.
Require Import riscv.Run.
Require Import riscv.util.Monads.
Require Import riscv.MkMachineWidth.
Require Import coqutil.Map.Interface.
Require Import riscv.Words32Naive.
Require Import riscv.DefaultMemImpl32.
Require Import coqutil.Map.Z_keyed_SortedListMap.
Require coqutil.Map.SortedList.

Existing Instance DefaultRiscvState.

Definition fib6_riscv: list MachineInt := [ (* TODO should be "word32", not MachineInt *)
  Ox"00600993";         (* li s3,6 *)
  Ox"00000a13";         (* li s4,0 *)
  Ox"00100913";         (* li s2,1 *)
  Ox"00000493";         (* li s1,0 *)
  Ox"0140006f";         (* j 101e0 <main+0x44> *)
  Ox"012a0ab3";         (* add s5,s4,s2 *)
  Ox"00090a13";         (* mv s4,s2 *)
  Ox"000a8913";         (* mv s2,s5 *)
  Ox"00148493";         (* addi s1,s1,1 *)
  Ox"ff34c8e3"          (* blt s1,s3,101d0 <main+0x34> *)
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

Definition RiscvMachine := riscv.RiscvMachine.RiscvMachine Register Empty_set.
Definition RiscvMachineL := riscv.RiscvMachine.RiscvMachine Register LogEvent.

(* This example uses the memory only as instruction memory
   TODO make an example which uses memory to store data *)
Definition zeroedRiscvMachine: RiscvMachine := {|
  getRegs := map.empty;
  getPc := ZToReg 0;
  getNextPc := ZToReg 4;
  getMem := map.empty;
  getLog := nil;
|}.

Definition zeroedRiscvMachineL: RiscvMachineL :=
  upgrade zeroedRiscvMachine nil.

Definition initialRiscvMachineL(imem: list MachineInt): RiscvMachineL :=
  putProgram imem (ZToReg 0) zeroedRiscvMachineL.

Definition run: nat -> RiscvMachineL -> (option unit) * RiscvMachineL := run.
 (* @run BitWidths32 MachineWidth32 (OState RiscvMachineL) (OState_Monad _) _ _ _ *)

Definition fib6_L_final(fuel: nat): RiscvMachineL :=
  match run fuel (initialRiscvMachineL fib6_riscv) with
  | (answer, state) => state
  end.

Definition fib6_L_res(fuel: nat): word32 :=
  match map.get (fib6_L_final fuel).(getRegs) 18 with
  | Some v => v
  | None => word.of_Z 0
  end.

Definition fib6_L_trace(fuel: nat): list (LogItem LogEvent) :=
  (fib6_L_final fuel).(getLog).

(* only uncomment this if you're sure there are no admits in the computational parts,
   otherwise this will eat all your memory *)

Eval vm_compute in (fib6_L_trace 50).

Lemma fib6_res_is_13_by_running_it: exists fuel, fib6_L_res fuel = word.of_Z 13.
  exists 50%nat.
  reflexivity.
Qed.
