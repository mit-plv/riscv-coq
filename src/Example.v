Require Import Coq.Lists.List.
Import ListNotations.
Require Import riscv.Riscv.
Require Import riscv.RiscvBitWidths32.
Require Import bbv.HexNotationZ.
Require Import Coq.ZArith.BinInt.
Require Import bbv.WordScope.
Require Import riscv.Utility.
Require Import riscv.Memory.
Require Import riscv.Minimal.
Require Import riscv.Run.
Require Import riscv.FunctionMemory.

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

Open Scope Z_scope.

Goal False.
  set (l := map (decode 32) fib6_riscv).
  cbv in l.
  (* decoder seems to work :) *)
Abort.

Definition RiscvMachine := @RiscvMachine _ (mem 32).

(* This example uses the memory only as instruction memory
   TODO make an example which uses memory to store data *)
Definition zeroedRiscvMachine: RiscvMachine := {|
  machineMem := const_mem $0;
  registers := fun (r: Register) => $0;
  pc := $0;
  nextPC := $4;
  exceptionHandlerAddr := -4;
|}.

Definition initialRiscvMachine(imem: list MachineInt): RiscvMachine :=
  putProgram (map (@ZToWord 32) imem) zeroedRiscvMachine.

(* TODO here the option used to encode selection in execute bubbles up until here,
   how can we avoid this? *)
Definition fib6_L_final(fuel: nat): option RiscvMachine :=
  match run fuel (initialRiscvMachine fib6_riscv) with
  | Some (answer, state) => Some state
  | None => None
  end.

Definition fib6_L_res(fuel: nat): option (word wXLEN) :=
  match fib6_L_final fuel with
  | Some r => Some (r.(registers) 18)
  | None => None
  end.

(*
Definition fib6_L_trace(fuel: nat): option (list TraceEvent) :=
  r <- fib6_L_final fuel;
  Return (r.(executionTrace)).
*)

Transparent wlt_dec.

(* only uncomment this if you're sure there are no admits in the computational parts,
   otherwise this will eat all your memory *)

Eval cbv in (load_byte_list (initialRiscvMachine fib6_riscv).(machineMem) $0 40).

Eval cbv in (load_word_list (initialRiscvMachine fib6_riscv).(machineMem) $0 10).

Eval cbv in (fib6_L_res 27).

Lemma fib6_res_is_13_by_running_it: exists fuel, fib6_L_res fuel = $13.
  exists 50%nat.
  cbv.
Abort.

*)
