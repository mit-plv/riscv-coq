Require Import Coq.Lists.List.
Require Import Coq.derive.Derive.
Require Import coqutil.Z.Lia.
Import ListNotations.
Require Import coqutil.Decidable.
Require Import coqutil.Word.Naive.
Require Import coqutil.Word.Properties.
Require Import riscv.Spec.Machine.
Require Import riscv.Spec.Decode.
Require Import riscv.Spec.Execute.
Require Import Coq.ZArith.BinInt. Local Open Scope Z_scope.
Require Import riscv.Utility.Utility.
Require Import riscv.Utility.PowerFunc.
Require Import riscv.Platform.Memory.
Require Import riscv.Utility.Monads. Import MonadNotations.
Require Import riscv.Utility.MkMachineWidth.
Require Import riscv.Utility.Words32Naive.
Require Import coqutil.Z.HexNotation.
Require Import riscv.Spec.PseudoInstructions.
Require Import riscv.Utility.RegisterNames.

(* note: this representation is not unique and stores at the same address don't simplify,
   but the advantage is that Array literals don't contain eqb functions that cbv could
   try simplifying even when its arguments are not concrete *)
Inductive Array(T U: Type): Type :=
| const(u: U)
| store(a: Array T U)(i: T)(u: U).
Arguments const {_} {_} _.
Arguments store {_} {_}.

Fixpoint select{T U: Type}{eqbT: T -> T -> bool}{eqbT_spec: EqDecider eqbT}(a: Array T U)(i: T): U :=
  match a with
  | const u => u
  | store a' i' u => if eqbT i i' then u else select a' i
  end.

Record MachineState := mkMachineState {
  Regs: Array Register word;
  Pc: word;
  NextPc: word;
  Prog: Array word InstructionI;
}.

Definition withRegs   x s := mkMachineState x        (Pc s) (NextPc s) (Prog s).
Definition withPc     x s := mkMachineState (Regs s) x      (NextPc s) (Prog s).
Definition withNextPc x s := mkMachineState (Regs s) (Pc s) x          (Prog s).
Definition withProg   x s := mkMachineState (Regs s) (Pc s) (NextPc s) x       .

Import riscv.Utility.Monads.OStateOperations.

Definition fail_if_None{R}(o: option R): OState MachineState R :=
  match o with
  | Some x => Return x
  | None => fail_hard
  end.

Definition update(f: MachineState -> MachineState): OState MachineState unit :=
  m <- get; put (f m).

(* not interested in memory in this case study *)
Definition loadN(n: nat)(kind: SourceType)(a: word): OState MachineState (HList.tuple byte n) := fail_hard.
Definition storeN(n: nat)(kind: SourceType)(a: word)(v: HList.tuple byte n): OState MachineState unit :=
  fail_hard.

Instance IsRiscvProgram: RiscvProgram (OState MachineState) word :=  {
  getRegister reg :=
    if Z.eq_dec reg Register0 then
      Return (ZToReg 0)
    else
      if ((0 <? reg) && (reg <? 32))%bool then
        mach <- get;
        Return (select mach.(Regs) reg)
      else
        fail_hard;

  setRegister reg v :=
    if Z.eq_dec reg Register0 then
      Return tt
    else
      if ((0 <? reg) && (reg <? 32))%bool then
        update (fun mach => withRegs (store mach.(Regs) reg v) mach)
      else
        fail_hard;

  getPC := mach <- get; Return mach.(Pc);

  setPC newPC := update (withNextPc newPC);

  loadByte   := loadN 1;
  loadHalf   := loadN 2;
  loadWord   := loadN 4;
  loadDouble := loadN 8;

  storeByte   := storeN 1;
  storeHalf   := storeN 2;
  storeWord   := storeN 4;
  storeDouble := storeN 8;

  makeReservation  addr := fail_hard;
  clearReservation addr := fail_hard;
  checkReservation addr := fail_hard;
  getCSRField f := fail_hard;
  setCSRField f v := fail_hard;
  getPrivMode := fail_hard;
  setPrivMode v := fail_hard;
  fence _ _ := fail_hard;

  endCycleNormal := update (fun m => (withPc m.(NextPc)
                                     (withNextPc (word.add m.(NextPc) (word.of_Z 4)) m)));

  (* fail hard if exception is thrown because at the moment, we want to prove that
     code output by the compiler never throws exceptions *)
  endCycleEarly{A: Type} := fail_hard;
  }.

Definition loadInstruction(a: word): OState MachineState Instruction :=
  s <- get; Return (IInstruction (select s.(Prog) a)).

Definition run1: OState MachineState unit :=
  pc <- getPC;
  inst <- loadInstruction pc;
  execute inst;;
  endCycleNormal.

(* Note: this only works as long as we don't use endCycleEarly, because otherwise
   all the remaining cycles (instead of just all the remaining operations *within*
   the current cycle) are skipped. *)
Definition runN(n: nat): OState MachineState unit := power_func (fun m => run1;; m) n (Return tt).

Definition zeroRegs: Array Register word := const (word.of_Z 0).

Fixpoint prog2Array(l: list InstructionI)(start: word): Array word InstructionI :=
  match l with
  | nil => const InvalidI
  | i :: rest => store (prog2Array rest (word.add start (word.of_Z 4))) start i
  end.

Definition initialState(initialRegs: Array Register word)(prog: list InstructionI): MachineState := {|
  Regs := initialRegs;
  Pc := word.of_Z 0;
  NextPc := word.of_Z 4;
  Prog := prog2Array prog (word.of_Z 0);
|}.

Definition runLinear(initialRegs: Array Register word)(prog: list InstructionI): MachineState :=
  snd (runN (List.length prog) (initialState initialRegs prog)).

(* t1 = t2 - t1 - 1 *)
Definition prog1A := [
  Sub t1 t2 t1;
  Addi t1 t1 (-1)
].

(* t1 = t2 + ~t1 *)
Definition prog1B := [
  Xori t1 t1 (-1);
  Add t1 t2 t1
].

Derive prog1Ares
  SuchThat (forall r0, prog1Ares r0 = Regs (runLinear r0 prog1A))
  As run1_correct.
Proof.
  intros.
  unfold runLinear, initialState.
  match goal with
  | |- context [List.length ?l] => let r := eval cbv in (List.length l) in change (List.length l) with r
  end.
  match goal with
  | |- context [prog2Array ?P ?A] =>
    let r := eval cbv in (prog2Array P A) in change (prog2Array P A) with r
  end.
  unfold runN, power_func.
  unfold run1 at 1.
  unfold Bind, Return, OState_Monad.
  unfold getPC, IsRiscvProgram, get, Bind, OState_Monad, Pc, Return, loadInstruction.
  unfold get, Bind, OState_Monad, Return.
  match goal with
  | |- context[select ?p ?i] => let r := eval cbv in (select p i) in change (select p i) with r
  end.
  unfold execute, ExecuteI.execute.
  unfold getRegister, setRegister, update, get, put, Bind, OState_Monad, endCycleNormal.
  repeat match goal with
  | |- context[match ?b in bool return ?r with true => ?c | false => ?d end] =>
       change (match  b in bool return  r with true =>  c | false =>  d end) with c
  | |- context[match ?b in bool return ?r with true => ?c | false => ?d end] =>
       change (match  b in bool return  r with true =>  c | false =>  d end) with d
  | |- context[match ?b in sumbool _ _ return ?r with right _ _ => ?c | left _ _ => ?d end] =>
       change (match  b in sumbool _ _ return  r with right _ _ =>  c | left _ _ =>  d end) with c
  | |- context[match ?b in sumbool _ _ return ?r with right _ _ => ?c | left _ _ => ?d end] =>
       change (match  b in sumbool _ _ return  r with right _ _ =>  c | left _ _ =>  d end) with d
  | |- _ => progress cbv beta iota zeta
  | |- _ => progress cbv [Regs Pc NextPc Prog withRegs withPc withNextPc withProg]
  end.
  unfold run1 at 1.
  unfold Bind, Return, OState_Monad.
  unfold getPC, IsRiscvProgram.
  unfold get, Bind, OState_Monad, Pc, Return.
  unfold loadInstruction.
  unfold get, Bind, OState_Monad, Return.
  match goal with
  | |- context[select ?p ?i] => let r := eval cbv in (select p i) in change (select p i) with r
  end.
  unfold execute, ExecuteI.execute.
  unfold getRegister, setRegister, update, get, put, Bind, OState_Monad, endCycleNormal.
  repeat match goal with
  | |- context[match ?b in bool return ?r with true => ?c | false => ?d end] =>
       change (match  b in bool return  r with true =>  c | false =>  d end) with c
  | |- context[match ?b in bool return ?r with true => ?c | false => ?d end] =>
       change (match  b in bool return  r with true =>  c | false =>  d end) with d
  | |- context[match ?b in sumbool _ _ return ?r with right _ _ => ?c | left _ _ => ?d end] =>
       change (match  b in sumbool _ _ return  r with right _ _ =>  c | left _ _ =>  d end) with c
  | |- context[match ?b in sumbool _ _ return ?r with right _ _ => ?c | left _ _ => ?d end] =>
       change (match  b in sumbool _ _ return  r with right _ _ =>  c | left _ _ =>  d end) with d
  | |- _ => progress cbv beta iota zeta
  | |- _ => progress cbv [Regs Pc NextPc Prog withRegs withPc withNextPc withProg]
  end.
  cbv [snd].
  subst prog1Ares.
  reflexivity.
Qed.
