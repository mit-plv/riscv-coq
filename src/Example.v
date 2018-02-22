Require Import Coq.Lists.List.
Import ListNotations.
Require Import riscv.Riscv.
Require Import riscv.RiscvBitWidths32.
Require Import bbv.HexNotation.
Require Import Coq.ZArith.BinInt.
Require Import bbv.WordScope.
Require Import riscv.Memory.
Require Import riscv.Run.

Definition fib6_riscv: list MachineInt := [ (* TODO should be "word 32", not MachineInt *)
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
  set (l := map decode fib6_riscv).
  cbv in l.
  (* decoder seems to work :) *)
Abort.

Definition initialRiscvMachine(imem: list MachineInt): RiscvMachine := {|
  machineMem := no_mem _; (* TODO *)
  registers := fun (r: Register) => $0;
  pc := $0;
  nextPC := $4;
  exceptionHandlerAddr := wneg $4;
|}.

Definition fib6_L_final(fuel: nat): RiscvMachine :=
  execState (run fuel) (initialRiscvMachine fib6_riscv).

Definition fib6_L_res(fuel: nat): word wXLEN :=
  (fib6_L_final fuel).(registers) (WO~1~0~0~1~0)%word.

(*
Definition fib6_L_trace(fuel: nat): list TraceEvent :=
  (fib6_L_final fuel).(executionTrace).
*)

Transparent wlt_dec.

(* TODO will only work once we don't have any admits in computational parts

Eval cbv in (fib6_L_trace 50).

Lemma fib6_res_is_13_by_running_it: exists fuel, fib6_L_res fuel = $13.
  exists 50%nat.
  cbv.
  reflexivity.
Qed.
*)
