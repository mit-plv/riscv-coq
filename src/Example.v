Require Import Coq.Lists.List.
Import ListNotations.
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
Require Import riscv.MachineWidth32.

Existing Instance DefaultRiscvState.

Instance FunctionRegisterFile: RegisterFileFunctions Register word32 := {|
  RegisterFile := Register -> word32;
  getReg(rf: Register -> word32) := rf;
  setReg(rf: Register -> word32)(r: Register)(v: word32) :=
    fun r' => if (Z.eqb r' r) then v else rf r';
  initialRegs := fun r => ZToReg 0;
|}.

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

Open Scope Z_scope.

Goal False.
  set (l := map (decode RV32IM) fib6_riscv).
  cbv in l.
  (* decoder seems to work :) *)
Abort.

Local Set Primitive Projections.
Require Import coqutil.Macros.subst coqutil.Macros.unique coqutil.Map.Interface.
Require Coq.Lists.List.
Require Coq.Logic.Eqdep_dec.

(* TODO: move me? *)
Definition minimize_eq_proof{A: Type}(eq_dec: forall (x y: A), {x = y} + {x <> y}){x y: A}    (pf: x = y): x = y :=
  match eq_dec x y with
  | left p => p
  | right n => match n pf: False with end
  end.

Module Import parameters.
  Local Set Primitive Projections.
  Class parameters := {
    key : Type;
    value : Type;
    key_eqb : key -> key -> bool;
    key_ltb : key -> key -> bool
  }.
End parameters. Notation parameters := parameters.parameters.

Section SortedList.
  Context {p : unique! parameters}.
  Fixpoint put m (k:key) (v:value) : list (key * value) :=
    match m with
    | nil => cons (k, v) nil
    | cons (k', v') m' =>
      if key_eqb k k'
      then cons (k, v) m'
      else
        if key_ltb k k'
        then cons (k, v) m
        else cons (k', v') (put m' k v)
    end.
  Fixpoint remove m (k:key) : list (key * value) :=
    match m with
    | nil => nil
    | cons (k', v') m' =>
      if key_eqb k k'
      then m'
      else
        if key_ltb k k'
        then m
        else cons (k', v') (remove m' k)
    end.
  Fixpoint sorted (m : list (key * value)) :=
    match m with
    | cons (k1, _) ((cons (k2, _) m'') as m') => andb (key_ltb k1 k2) (sorted m')
    | _ => true
    end.
  Record rep := { value : list (key * value) ; ok : sorted value = true }.
  Lemma sorted_put m k v : sorted m = true -> sorted (put m k v) = true. Admitted.
  Lemma sorted_remove m k : sorted m = true -> sorted (remove m k) = true. Admitted.
  Definition map : map.map key parameters.value :=
    let wrapped_put m k v := Build_rep (put (value m) k v) (minimize_eq_proof Bool.bool_dec (sorted_put _ _ _ (ok m))) in
    let wrapped_remove m k := Build_rep (remove (value m) k) (minimize_eq_proof Bool.bool_dec (sorted_remove _ _ (ok m))) in
    {|
    map.rep := rep;
    map.empty := Build_rep nil eq_refl;
    map.get m k := match List.find (fun p => key_eqb k (fst p)) (value m) with
                   | Some (_, v) => Some v
                   | None => None
                   end;
    map.put := wrapped_put;
    map.remove := wrapped_remove;
    map.putmany m1 m2 := List.fold_right (fun '(k, v) m => wrapped_put m k v) m1 (value m2)
  |}.
End SortedList.

Existing Instance map.

Set Refine Instance Mode.
Instance params: parameters := {
    key := word32;
    value := byte;
    key_eqb := word.eqb;
    key_ltb := word.ltu;
}.
Instance bar: Interface.map.map word32 byte := @map _.

Module Test.
  Definition emp: bar := map.empty.
  Eval cbv in (map.get (map.put (map.put emp (word.of_Z 3) (word.of_Z 33)) (word.of_Z 3) (word.of_Z 44)) (word.of_Z 3)).
End Test.

Definition RiscvMachine := riscv.RiscvMachine.RiscvMachine Register word32 Empty_set.
Definition RiscvMachineL := riscv.RiscvMachine.RiscvMachine Register word32 LogEvent.

(* This example uses the memory only as instruction memory
   TODO make an example which uses memory to store data *)
Definition zeroedRiscvMachine: RiscvMachine := {|
  getRegs := initialRegs;
  getPc := ZToReg 0;
  getNextPc := ZToReg 4;
  getMem := map.empty;
  getLog := nil;
|}.

Definition zeroedRiscvMachineL: RiscvMachineL :=
  upgrade zeroedRiscvMachine [(EvLoadWord 12345 (InvalidInstruction 777), [], [])].

Definition initialRiscvMachineL(imem: list MachineInt): RiscvMachineL :=
  putProgram imem (ZToReg 0) zeroedRiscvMachineL.

Definition run: nat -> RiscvMachineL -> (option unit) * RiscvMachineL := run.
 (* @run BitWidths32 MachineWidth32 (OState RiscvMachineL) (OState_Monad _) _ _ _ *)

Definition fib6_L_final(fuel: nat): RiscvMachineL :=
  match run fuel (initialRiscvMachineL fib6_riscv) with
  | (answer, state) => state
  end.

Definition fib6_L_res(fuel: nat): word32 :=
  (fib6_L_final fuel).(getRegs) 18.

Definition fib6_L_trace(fuel: nat): list (LogItem word32 LogEvent) :=
  (fib6_L_final fuel).(getLog).

(* only uncomment this if you're sure there are no admits in the computational parts,
   otherwise this will eat all your memory *)

Eval vm_compute in (fib6_L_trace 50).

Lemma fib6_res_is_13_by_running_it: exists fuel, fib6_L_res fuel = ZToReg 13.
  exists 50%nat.
  reflexivity.
Qed.
