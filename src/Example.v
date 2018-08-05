Require Import Coq.Lists.List.
Import ListNotations.
Require Import riscv.Riscv.
Require Import riscv.util.BitWidth32.
Require Import bbv.HexNotationZ.
Require Import Coq.ZArith.BinInt.
Require Import bbv.WordScope.
Require Import riscv.Utility.
Require Import riscv.Memory.
Require Import riscv.Minimal.
Require Import riscv.MinimalLogging.
Require Import riscv.Run.
Require Import riscv.ListMemory.
Require Import riscv.util.Monads.

Existing Instance DefaultRiscvState.

Instance FunctionRegisterFile: RegisterFile (Register -> word wXLEN) Register (word wXLEN) := {|
  getReg(rf: Register -> word wXLEN) := rf;
  setReg(rf: Register -> word wXLEN)(r: Register)(v: word wXLEN) :=
    fun r' => if (Z.eqb r' r) then v else rf r';
  initialRegs := fun r => $0;
|}.

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
  set (l := map (decode RV32IM) fib6_riscv).
  cbv in l.
  (* decoder seems to work :) *)
Abort.

Definition RiscvMachine := @RiscvMachine (word 32) (mem wXLEN) (Register -> word wXLEN).

(* This example uses the memory only as instruction memory
   TODO make an example which uses memory to store data *)
Definition zeroedRiscvMachineCore: RiscvMachineCore := {|
  registers := initialRegs;
  pc := $0;
  nextPC := (natToWord 32 4);
  exceptionHandlerAddr := 3;
|}.

Definition zeroedRiscvMachine: RiscvMachine := {|
    core := zeroedRiscvMachineCore;
    machineMem := zero_mem 100;
|}.

Definition zeroedRiscvMachineL: RiscvMachineL := {|
    machine := zeroedRiscvMachine;
    log := nil;
|}.

Definition initialRiscvMachineL(imem: list MachineInt): RiscvMachineL :=
  putProgram (map (@ZToWord 32) imem) $0 zeroedRiscvMachineL.

Definition run: nat -> RiscvMachineL -> (option unit) * RiscvMachineL := run.
 (* @run BitWidths32 MachineWidth32 (OState RiscvMachineL) (OState_Monad _) _ _ _ *)

Definition fib6_L_final(fuel: nat): RiscvMachineL :=
  match run fuel (initialRiscvMachineL fib6_riscv) with
  | (answer, state) => state
  end.

Definition fib6_L_res(fuel: nat): word wXLEN :=
  (fib6_L_final fuel).(machine).(core).(registers) 18.

Definition fib6_L_trace(fuel: nat): Log :=
  (fib6_L_final fuel).(log).

Transparent wlt_dec.

(* only uncomment this if you're sure there are no admits in the computational parts,
   otherwise this will eat all your memory *)

(* 
TODO make sure this works again!
Eval cbv in (fib6_L_trace 50).
 *)

(*
Eval cbv in (fib6_L_res 27).
Eval cbv in (fib6_L_res 50).
 *)

Lemma fib6_res_is_13_by_running_it: exists fuel, fib6_L_res fuel = $13.
  exists 50%nat.
  reflexivity.
Qed.
