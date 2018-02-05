Require Import Coq.Lists.List.
Import ListNotations.
Require Import riscv.Riscv.
Require Import riscv.RiscvBitWidths32.


Instance NatName: NameWithEq := {| name := nat |}.

Definition var: Set := (@name NatName).
Definition Reg: Set := (@name NatName).

Definition var_a: var := 0.
Definition var_b: var := 1.
Definition var_c: var := 2.
Definition var_i: var := 3.

(* stores fib(6) into register var_b (inefficient compiler-generated assembly) *)
Definition fib6_riscv: list Instruction := [
  Addi (RegS 4) RegO $ (0);
  Add (RegS var_a) RegO (RegS 4);
  Addi (RegS 5) RegO $ (1);
  Add (RegS var_b) RegO (RegS 5);
  Addi (RegS 6) RegO $ (0);
  Add (RegS var_i) RegO (RegS 6);
  Add (RegS 7) RegO (RegS var_i);
  Addi (RegS 8) RegO $ (6);
  Sltu (RegS 9) (RegS 7) (RegS 8);
  Beq (RegS 9) RegO ($ (2) ^* $ (13));
  Add (RegS 10) RegO (RegS var_a);
  Add (RegS 11) RegO (RegS var_b);
  Add (RegS 12) (RegS 10) (RegS 11);
  Add (RegS var_c) RegO (RegS 12);
  Add (RegS 13) RegO (RegS var_b);
  Add (RegS var_a) RegO (RegS 13);
  Add (RegS 14) RegO (RegS var_c);
  Add (RegS var_b) RegO (RegS 14);
  Add (RegS 15) RegO (RegS var_i);
  Addi (RegS 16) RegO $ (1);
  Add (RegS 17) (RegS 15) (RegS 16);
  Add (RegS var_i) RegO (RegS 17);
  Jal RegO (^~ ($ (2) ^* $ (17)))
].

Definition initialRiscvMachine(imem: list Instruction): RiscvMachine := {|
  instructionMem := fun (i: word wXLEN) => nth (Nat.div (wordToNat i) 4) imem InfiniteJal;
  registers := fun (r: Reg) => $0;
  pc := $0;
  exceptionHandlerAddr := wneg $4;
|}.

Definition fib6_L_final(fuel: nat): RiscvMachine :=
  execState (run fuel) (initialRiscvMachine fib6_riscv).

Definition fib6_L_res(fuel: nat): word wXLEN :=
  (fib6_L_final fuel).(registers) var_b.

Transparent wlt_dec.

Lemma fib6_res_is_13_by_running_it: exists fuel, fib6_L_res fuel = $13.
  exists 200. cbv. reflexivity.
Qed.
