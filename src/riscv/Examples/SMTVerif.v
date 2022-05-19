Require Import Coq.Lists.List.
Require Import Coq.Logic.Classical_Prop.
Import ListNotations.
Require Import coqutil.Decidable.
Require Import coqutil.Word.Naive.
Require Import riscv.Spec.Machine.
Require Import riscv.Spec.Decode.
Require Import riscv.Spec.Execute.
Require Import Coq.ZArith.BinInt. Local Open Scope Z_scope.
Require Import riscv.Utility.Utility.
Require Import riscv.Utility.PowerFunc.
Require Import riscv.Utility.Monads. Import MonadNotations.
Require Import riscv.Utility.MkMachineWidth.
Require Import riscv.Utility.Words32Naive.
Require Import riscv.Spec.PseudoInstructions.
Require Import riscv.Utility.InstructionCoercions. Open Scope ilist_scope.
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
  Prog: Array word Instruction;
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

#[global] Instance IsRiscvProgram: RiscvProgram (OState MachineState) word :=  {
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
  s <- get; Return (select s.(Prog) a).

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

Fixpoint prog2Array(l: list Instruction)(start: word): Array word Instruction :=
  match l with
  | nil => const (InvalidInstruction 0)
  | i :: rest => store (prog2Array rest (word.add start (word.of_Z 4))) start i
  end.

Definition initialState(initialRegs: Array Register word)(prog: list Instruction): MachineState := {|
  Regs := initialRegs;
  Pc := word.of_Z 0;
  NextPc := word.of_Z 4;
  Prog := prog2Array prog (word.of_Z 0);
|}.

Definition runLinear(initialRegs: Array Register word)(prog: list Instruction): MachineState :=
  snd (runN (List.length prog) (initialState initialRegs prog)).

(* t1 = t2 * t3 *)
Definition prog1A: list Instruction := [[
  Mul t1 t2 t3
]].

(* Optimization of prog1A that is only valid if t3=5:
   t1 = (t2 << 2) + t2 *)
Definition prog1B: list Instruction := [[
  Slli t1 t2 2;
  Add t1 t1 t2
]].

(* t1 = t2 - t1 - 1 *)
Definition prog2A: list Instruction := [[
  Sub t1 t2 t1;
  Addi t1 t1 (-1)
]].

(* t1 = t2 + ~t1 *)
Definition prog2B: list Instruction := [[
  Xori t1 t1 (-1);
  Add t1 t2 t1
]].

(* t3 = 31
   t1 = t2 * t3 *)
Definition prog3A: list Instruction := [[
  Addi t3 zero 31;
  Mul t1 t2 t3
]].

(* t1 = (t2 << 5) - t2
   t3 = 31 *)
Definition prog3B: list Instruction := [[
  Slli t1 t2 5;
  Sub t1 t1 t2;
  Addi t3 zero 31 (* <-- could be removed later by dead code elimination *)
]].

Ltac reduce_to_stores :=
  repeat match goal with
         | |- ?LHS = ?RHS => progress (let l := eval hnf in LHS in change LHS with l;
                                       let r := eval hnf in RHS in change RHS with r)
         | |- context[store ?a _ _] => progress let r := eval hnf in a in change a with r
         end.

Goal forall regs,
    select regs t3 = ZToReg 5 ->
    Regs (runLinear regs prog1A) = Regs (runLinear regs prog1B).
Abort.

Goal forall regs,
    Regs (runLinear regs prog2A) = Regs (runLinear regs prog2B).
Abort.

Goal forall regs,
    Regs (runLinear regs prog3A) = Regs (runLinear regs prog3B).
Proof.
  intros.
  reduce_to_stores.
  unfold t1, t2, t3 in *.
  apply NNPP.
  let H := fresh "NegGoal" in intro H.
  repeat match goal with
         | H: _ |- _ => revert H
         end.

Notation "'and' A B" := (Logic.and A B) (at level 10, A at level 0, B at level 0).
Notation "'or' A B" := (Logic.or A B) (at level 10, A at level 0, B at level 0).
Notation "+ A B" := (Z.add A B) (at level 10, A at level 0, B at level 0).
Notation "< A B" := (Z.lt A B) (at level 10, A at level 0, B at level 0).
Notation "<= A B" := (Z.le A B) (at level 10, A at level 0, B at level 0).
Notation "- A B" := (Z.sub A B) (at level 10, A at level 0, B at level 0).
(* Notation "- 1" := minusone (at level 10, format "-  1"). omits space, why? *)
Notation "* A B" := (Z.mul A B) (at level 10, A at level 0, B at level 0, format " *  A  B").
Notation "'mod' A B" := (Z.modulo A B) (at level 10, A at level 0, B at level 0).
Notation "^ A B" := (Z.pow A B) (at level 10, A at level 0, B at level 0).
Notation "= A B" := (@eq _ A B) (at level 10, A at level 0, B at level 0).
Notation "'exists' ( ( x T ) ) b" := (exists x: T, b) (at level 10, T at level 0, b at level 0).
Notation "'not' A" := (negb A) (at level 10, A at level 0).
Notation "'ite' b thn els" := (if b then thn else els)
  (at level 10, b at level 0, thn at level 0, els at level 0).
Notation "'(_' 'bv' B 32 )" := (ZToReg B) (at level 0, format "'(_'  'bv' B  32 )").
Notation "#xffffffff" := (ZToReg (-1)) (at level 0).
Notation "'not' ( = A B )" := (A <> B) (at level 10, A at level 0, B at level 0, format "'not'  ( =  A  B )").

Notation "'bvadd' A B" := (add A B) (at level 10, A at level 0, B at level 0).
Notation "'bvsub' A B" := (sub A B) (at level 10, A at level 0, B at level 0).
Notation "'bvmul' A B" := (mul A B) (at level 10, A at level 0, B at level 0).
Notation "'bvor' A B" := (or A B) (at level 10, A at level 0, B at level 0).
Notation "'bvxor' A B" := (xor A B) (at level 10, A at level 0, B at level 0).
Notation "'bvand' A B" := (and A B) (at level 10, A at level 0, B at level 0).
Notation "'bvshl' A '(_' 'bv' B 32 )" := (sll A B)
  (at level 10, A at level 0, B at level 0, format "'bvshl'  A  '(_'  'bv' B  32 )").
Notation "'bvlshr' A '(_' 'bv' B 32 )" := (srl A B)
  (at level 10, A at level 0, B at level 0, format "'bvlshr'  A  '(_'  'bv' B  32 )").
Notation "'bvashr' A '(_' 'bv' B 32 )" := (sra A B)
  (at level 10, A at level 0, B at level 0, format "'bvashr'  A  '(_'  'bv' B  32 )").

Notation "'Int'" := Z.
Notation "'(_' 'BitVec' '32)'" := (@word.rep _ _).
Notation "'(declare-const' x T ) P" := (forall x: T, P)
  (at level 0, x at level 0, T at level 0, P at level 0, format "'(declare-const'  x  T ) '//' P").
Notation "'(assert' P ) Q" := (P -> Q)
  (at level 0, P at level 0, Q at level 0, format "'(assert'  P ) '//' Q").
Notation "'(check-sat)'" := False.

Set Printing Width 70.
Set Printing Coercions. (* COQBUG https://github.com/coq/coq/issues/13432 *)
match goal with
| |- ?G => idtac G
end.

Abort.
