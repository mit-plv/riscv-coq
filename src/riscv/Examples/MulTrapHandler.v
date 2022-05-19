Require Import coqutil.Z.Lia.
Require Import coqutil.Word.Naive.
Require Import coqutil.Word.Properties.
Require Coq.Strings.String. Open Scope string_scope.
Require Import Coq.Lists.List. Import ListNotations.
Require Import riscv.Utility.InstructionCoercions. Open Scope ilist_scope.
Require Import riscv.Spec.Machine.
Require Import riscv.Spec.Decode.
Require Import riscv.Spec.PseudoInstructions.
Require Import riscv.Utility.RegisterNames.
Require Import Coq.ZArith.BinInt.
Require Import riscv.Utility.Utility.
Require Import riscv.Platform.Memory.
Require Import riscv.Platform.MinimalCSRsDet.
Require Import riscv.Platform.Run.
Require Import riscv.Utility.Monads.
Require Import riscv.Utility.MonadNotations.
Require Import riscv.Utility.MkMachineWidth.
Require Import riscv.Utility.Encode.
Require Import coqutil.Map.Interface.
Require Import riscv.Utility.Words32Naive.
Require Import riscv.Utility.DefaultMemImpl32.
Require Import coqutil.Map.Z_keyed_SortedListMap.
Require Import riscv.Utility.ExtensibleRecords. Import HnatmapNotations. Open Scope hnatmap_scope.
Require coqutil.Map.SortedList.
Require Import riscv.Examples.SoftmulInsts.
Require Import riscv.Platform.LogInstructionTrace.

(* note: these numbers must fit into a 12bit immediate, and should be small if we want to simulate
   execution inside Coq *)
Definition main_start: Z := 0.
Definition handler_start: Z := 32.
Definition handler_stack_start: Z := 512.
Definition heap_start: Z := 640.

(* mem[heap_start+8] := mem[heap_start] * mem[heap_start+4] *)
Definition main_insts := [[
  Lw t1 zero heap_start;
  Lw t2 zero (heap_start+4);
  Mul t3 t1 t2;
  Sw zero t3 (heap_start+8)
]].

Definition input1: Z := 5.
Definition input2: Z := 13.

Definition initial_datamem: Mem := Eval vm_compute in
      let m := map.of_tuple (Memory.footprint (word.of_Z handler_stack_start) 300)
                            (HList.tuple.unfoldn id 300 Byte.x00) in
      let m := unchecked_store_bytes 4 m (word.of_Z heap_start) (LittleEndian.split 4 input1) in
      unchecked_store_bytes 4 m (word.of_Z (heap_start+4)) (LittleEndian.split 4 input2).

Definition putProgram(m: Mem)(addr: Z)(prog: list Instruction): Mem :=
  unchecked_store_byte_list (word.of_Z addr) (RiscvMachine.Z32s_to_bytes (List.map encode prog)) m.

Definition initial_mem: Mem := Eval vm_compute in
      putProgram (putProgram initial_datamem main_start main_insts) handler_start handler_insts.

Definition FieldNames: natmap Type := MinimalCSRsDet.Fields (natmap.put nil exectrace ExecTrace).

Definition State: Type := hnatmap FieldNames.

Definition initial_regs :=
  map.of_tuple (key:=Z) (HList.tuple.unfoldn (Z.add 1) 31 1) (HList.tuple.unfoldn id 31 (word.of_Z (word:=Naive.word 32) 0)).

Definition initial_state: State := HNil
  [regs := initial_regs]
  [pc := word.of_Z 0]
  [nextPc := word.of_Z 4]
  [mem := initial_mem]
  [log := nil]
  [csrs := map.of_list ((CSRField.MTVecBase, (handler_start/4)) ::
                        (CSRField.MScratch, handler_stack_start) :: nil)]
  [exectrace := nil].

#[global] Instance IsRiscvMachine: RiscvProgram (StateAbortFail State) word :=
  AddExecTrace FieldNames (MinimalCSRsDet.IsRiscvMachine FieldNames).

(* success flag * final state *)
Fixpoint run(fuel: nat)(s: State): bool * State :=
  match fuel with
  | O => (true, s)
  | S fuel' => match Run.run1 RV32I s with
               | (Some _, s') => run fuel' s'
               | (None, s') => (false, s')
               end
  end.

Definition trace(fuel: nat): bool * ExecTrace :=
  match run fuel initial_state with
  | (isSuccess, final) => (isSuccess, final[exectrace])
  end.

(* fails, but that's excpected because it runs past the last instruction of main into unmapped memory
Eval vm_compute in trace 1000. *)

Goal Memory.loadWord initial_state[mem] (word.of_Z (heap_start+8)) = Some (LittleEndian.split 4 0).
Proof. reflexivity. Qed.

Goal Memory.loadWord initial_state[mem] (word.of_Z (heap_start+8)) =
     Some (LittleEndian.split 4 0).
Proof. reflexivity. Qed.

Goal Memory.loadWord (snd (run 1000 initial_state))[mem] (word.of_Z (heap_start+8)) =
     Some (LittleEndian.split 4 (input1 * input2)).
Proof. vm_compute. reflexivity. Qed.
