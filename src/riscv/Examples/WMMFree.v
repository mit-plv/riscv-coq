Require Import Coq.Lists.List. Import ListNotations.
Require Import coqutil.Decidable.
Require Import coqutil.Tactics.Tactics.
Require Import coqutil.Tactics.Simp.
Require Import riscv.Spec.Machine.
Require Import riscv.Spec.Execute.
Require Import riscv.Utility.Monads.
Require Import riscv.Utility.MonadNotations.
Require Import riscv.Utility.Utility.
Require Import riscv.Utility.Encode.
Require Import coqutil.Z.Lia.
Require Import coqutil.Map.Interface.
Require Import riscv.Platform.MaterializeRiscvProgram.
Require Import riscv.Utility.Words32Naive.
Require Import coqutil.Map.Z_keyed_SortedListMap.
Require Import coqutil.Map.OfFunc.
Require Import coqutil.Word.Properties.
Require Import coqutil.Z.prove_Zeq_bitwise.
Require Import Coq.ZArith.ZArith.
Require Import riscv.Utility.PowerFunc.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Logic.PropExtensionality.
Require Import Coq.derive.Derive.
Require Import riscv.Spec.Decode.

(* sub-relation *)
Definition subrel{A B: Type}(R1 R2: A -> B -> Prop): Prop :=
  forall a b, R1 a b -> R2 a b.

Definition unionrel{A B: Type}(R1 R2: A -> B -> Prop): A -> B -> Prop :=
  fun a b => R1 a b \/ R2 a b.

Definition invrel{A B: Type}(R: A -> B -> Prop): B -> A -> Prop := fun b a => R a b.

Definition composerel{A B C: Type}(R1: A -> B -> Prop)(R2: B -> C -> Prop): A -> C -> Prop :=
  fun a c => exists b, R1 a b /\ R2 b c.

Section Orders.
  Context {A: Type} (R: A -> A -> Prop).

  Definition irreflexive := forall a, ~ R a a.
  Definition asymmetric := forall a b, R a b -> ~ R b a.
  Definition transitive := forall a b c, R a b -> R b c -> R a c.

  Record strictPartialOrder := mkStrictPartialOrder {
    strictPartialOrder_irreflexive: irreflexive;
    strictPartialOrder_transitive: transitive;
  }.
  Lemma strictPartialOrder_asymmetric: strictPartialOrder -> asymmetric.
  Proof.
    intros [IR TR]. unfold irreflexive, transitive, asymmetric in *.
    intros. intro C. eapply IR. eauto.
  Qed.

  (* transitive (but not reflexive) closure *)
  Inductive trcl : A -> A -> Prop :=
  | TrclOne: forall a1 a2, R a1 a2 -> trcl a1 a2
  | TrclCons: forall a1 a2 a3, R a1 a2 -> trcl a2 a3 -> trcl a1 a3.

  Definition hasCycle := exists a, trcl a a.

  Definition acyclic := ~ hasCycle.
End Orders.

Definition TODO{T: Type}: T. Admitted.

(* Weak memory formalization following
   Kokologiannakis and Vafeiadis: HMC Model Checking for Hardware Memory Models, ASPLOS 2020

Errata:
- Algorithm 1, line 18: `\Phi(r);` should be `\Phi(r) <- v;`
*)

(* thread id *)
Definition Tid := nat.

Inductive Event :=
| InitEvent(x: word) (* event initializes the byte stored at address x (will say elsewhere to what value) *)
| ThreadEvent(t: Tid)(i: nat). (* the i-th event of thread t (will say elsewhere what happened) *)

Definition tid(e: Event): Tid :=
  match e with
  | InitEvent x => 0 (* error *)
  | ThreadEvent t i => t
  end.

(* serial id of event *)
Definition iid(e: Event): nat :=
  match e with
  | InitEvent x => 0 (* error *)
  | ThreadEvent t i => i
  end.

(* program order *)
Definition po(e1 e2: Event): Prop :=
  match e2 with
  | InitEvent _ => False
  | ThreadEvent t2 i2 =>
    match e1 with
    | InitEvent _ => True
    | ThreadEvent t1 i1 => t1 = t2 /\ i1 < i2
    end
  end.

Inductive Label :=
| ReadLabel(x: word)
| WriteLabel(x: word)(v: w8)
| FenceLabel
| ErrorLabel
| AbsentLabel.

Inductive EventTyp := ReadEvent | WriteEvent | FenceEvent | ErrorEvent | AbsentEvent.

Definition LabelTyp(l: Label): EventTyp :=
  match l with
  | ReadLabel _ => ReadEvent
  | WriteLabel _ _ => WriteEvent
  | FenceLabel => FenceEvent
  | ErrorLabel => ErrorEvent
  | AbsentLabel => AbsentEvent
  end.

Inductive Array(T U: Type): Type := mkArray (f: T -> U).
Arguments mkArray {_} {_}.
Definition select{T U: Type}(a: Array T U)(i: T): U :=
  match a with
  | mkArray f => f i
  end.
Definition Array2Fun{T U: Type}(a: Array T U): T -> U :=
  match a with
  | mkArray f => f
  end.
Definition store{T U: Type}{eqbT: T -> T -> bool}{eqbT_spec: EqDecider eqbT}(a: Array T U)(i: T)(u: U):
  Array T U := mkArray (fun j => if eqbT i j then u else Array2Fun a j).
Definition constArray(T U: Type)(u: U): Array T U := mkArray (fun _ => u).

(*Definition store{T U: Type}(a: Array T U)(i: T)(v: U): Array T U := *)
Definition set(T: Type) := Array T Prop.

Record Graph := mkGraph {
  (* label of each event, AbsentLabel means the event is not part of the graph *)
  Lab: Array Event Label;
  (* reads-from function: maps each read event to the write event of the same location
     that determines the read's value *)
  Rf: Array Event Event;
  (* address dependencies of memory accesses *)
  Addr: Array Event (set Event);
  (* data dependencies of writes *)
  Data: Array Event (set Event);
  (* control dependencies of events *)
  Ctrl: Array Event (set Event);
}.

Definition Events(G: Graph): set Event :=
  mkArray (fun e => select G.(Lab) e <> AbsentLabel).

Definition InitializationEvents(G: Graph): set Event :=
  mkArray (fun e => exists x v, e = InitEvent x /\ select G.(Lab) e = WriteLabel x v).

Definition ThreadEvents(G: Graph): set Event :=
  mkArray (fun e => exists t i, e = ThreadEvent t i /\ select G.(Lab) e <> AbsentLabel).

Definition ReadEvents(G: Graph): set Event :=
  mkArray (fun e => exists x, select G.(Lab) e = ReadLabel x).

Definition WriteEvents(G: Graph): set Event :=
  mkArray (fun e => exists x v, select G.(Lab) e = WriteLabel x v).

Definition FenceEvents(G: Graph): set Event :=
  mkArray (fun e => select G.(Lab) e = FenceLabel).

Definition ErrorEvents(G: Graph): set Event :=
  mkArray (fun e => select G.(Lab) e = ErrorLabel).

Definition Typ(G: Graph)(e: Event): EventTyp := LabelTyp (select G.(Lab) e).

Definition Loc(G: Graph)(e: Event): option word :=
  match select G.(Lab) e with
  | ReadLabel x => Some x
  | WriteLabel x v => Some x
  | FenceLabel => None
  | ErrorLabel => None
  | AbsentLabel => None
  end.

Definition w8zero: w8 := PrimitivePair.pair.mk Byte.x00 tt.

Definition Val(G: Graph)(e: Event): w8 :=
  match select G.(Lab) e with
  | ReadLabel x => w8zero
  | WriteLabel x v => v
  | FenceLabel => w8zero
  | ErrorLabel => w8zero
  | AbsentLabel => w8zero
  end.

Definition errorFree(G: Graph): Prop := forall e, select G.(Lab) e <> ErrorLabel.

Notation "x '\in' s" := (Array2Fun s x) (at level 70, no associativity).

(* reads-from relation: `RfRel g e1 e2` means "e2 reads from e1" *)
Inductive RfRel(G: Graph): Event -> Event -> Prop :=
  mkRfRel: forall r, r \in ReadEvents G -> RfRel G (select G.(Rf) r) r.

(* address dependency relation: `AddrRel e1 e2` means "e2 has an address dependency on e1" *)
Definition AddrRel(G: Graph)(r e: Event): Prop := r \in (select G.(Addr) e).
Definition DataRel(G: Graph)(r e: Event): Prop := r \in (select G.(Data) e).
Definition CtrlRel(G: Graph)(r e: Event): Prop := r \in (select G.(Ctrl) e).

Definition dependencyEdgesInProgramOrder(G: Graph): Prop :=
  subrel (AddrRel G) po /\ subrel (DataRel G) po /\ subrel (CtrlRel G) po.

Definition modificationOrder(G: Graph)(R: Event -> Event -> Prop): Prop :=
  strictPartialOrder R /\
  (forall e1 e2, R e1 e2 -> Typ G e1 = WriteEvent /\ Typ G e2 = WriteEvent /\ Loc G e1 = Loc G e2) /\
  (forall e1 e2, e1 \in WriteEvents G -> e2 \in WriteEvents G -> R e1 e2 \/ R e2 e1).

Definition NextEvent(e: Event): Event :=
  match e with
  | InitEvent x => e
  | ThreadEvent t i => ThreadEvent t (S i)
  end.

Infix "\U" := unionrel (at level 50, left associativity).
Infix "\;" := composerel (at level 41, right associativity).
Notation "R ^-1" := (invrel R) (at level 7).

Definition SC_acyclicity(G: Graph)(mo: Event -> Event -> Prop): Prop :=
  acyclic (po \U (RfRel G) \U mo \U ((RfRel G)^-1 \; mo)).

(* sequential consistency *)
Definition consSC(G: Graph): Prop := exists mo, modificationOrder G mo /\ SC_acyclicity G mo.

(* Examples of porf-acyclic models are SC, TSO, PSO, and RC11 *)
Definition porf_acyclic(G: Graph): Prop := acyclic (unionrel po (RfRel G)).

Definition prefix(G: Graph)(e: Event): set Event :=
  mkArray (fun e' => e \in ThreadEvents G /\
            trcl (unionrel (RfRel G) (unionrel (AddrRel G) (unionrel (DataRel G) (CtrlRel G)))) e' e).

(* Well-prefixed models include all the porf-acyclic ones,
   as well as ARMv7, ARMv8, IMM, LKMM, POWER, and RISC-V. *)
Definition wellPrefixed(G: Graph): Prop := forall e, ~ e \in prefix G e.

Record ThreadState := mkThreadState {
  Regs: Array Register word;
  Pc: word;
  NextPc: word;
  Prog: Array word InstructionI;
  CurrentEvent: Event;
  Deps: Array Register (set Event);
}.

Definition withRegs         x s := mkThreadState x        (Pc s) (NextPc s) (Prog s) (CurrentEvent s) (Deps s).
Definition withPc           x s := mkThreadState (Regs s) x      (NextPc s) (Prog s) (CurrentEvent s) (Deps s).
Definition withNextPc       x s := mkThreadState (Regs s) (Pc s) x          (Prog s) (CurrentEvent s) (Deps s).
Definition withProg         x s := mkThreadState (Regs s) (Pc s) (NextPc s) x        (CurrentEvent s) (Deps s).
Definition withCurrentEvent x s := mkThreadState (Regs s) (Pc s) (NextPc s) (Prog s) x                (Deps s).
Definition withDeps         x s := mkThreadState (Regs s) (Pc s) (NextPc s) (Prog s) (CurrentEvent s) x       .

Inductive M: Type -> Type :=
| Get{A: Type}(k: ThreadState -> M A): M A
| Put(s: ThreadState){A: Type}(k: M A): M A
| Ask{A: Type}(k: Graph -> M A): M A
(* picks a value satisfying P, or if none exists, rejects the graph *)
| RestrictGraph(P: Prop){A: Type}(k: M A): M A
| Ret{A: Type}(a: A): M A
(* could halt because the graph is rejected, because the program failed, or because the program is done *)
| HaltThread{A: Type}: M A.

Fixpoint bind{A B: Type}(m: M A){struct m}: (A -> M B) -> M B :=
  match m in (M T) return ((T -> M B) -> M B) with
  | Get k => fun f => Get (fun s => bind (k s) f)
  | Put s k => fun f => Put s (bind k f)
  | Ask k => fun f => Ask (fun G => bind (k G) f)
  | RestrictGraph P k => fun f => RestrictGraph P (bind k f)
  | Ret a => fun f => f a
  | HaltThread => fun f => HaltThread (* Note: Drops the continuation in f *)
  end.

#[global] Instance M_Monad: Monad M. refine ({|
  Bind := @bind;
  Return := @Ret
|}).
all: intros.
- reflexivity.
- induction m; simpl; try congruence; f_equal; extensionality s; apply H.
- revert B C f g.
  induction m; intros; simpl; try congruence; f_equal;
    try extensionality s; eauto.
Defined.

(* state monad: *)
Definition get: M ThreadState := Get Ret.
Definition put(s: ThreadState): M unit := Put s (Ret tt).

(* reader monad: *)
Definition ask: M Graph := Ask Ret.

(* assertion monad: *)
Definition assert_graph(P: Prop): M unit := RestrictGraph P (Ret tt).

Definition halt_thread{A: Type}: M A := HaltThread.

Definition reject_program{A: Type}: M A :=
  G <- ask; s <- get; assert_graph (select G.(Lab) s.(CurrentEvent) = ErrorLabel);; halt_thread.

Definition reject_graph{A: Type}: M A := assert_graph False;; halt_thread.

(* If we have a primitive program `p` of type `M A`, then `interp p G s1 s2 a` means that
   under the global given graph G, starting in thread state s1 can end in state s2
   and produce answer a. *)
Fixpoint interp{A: Type}(p: M A): Graph -> ThreadState -> ThreadState -> A -> Prop :=
  match p in (M T) return (Graph -> ThreadState -> ThreadState -> T -> Prop) with
  | Get k => fun G s1 s2 a => interp (k s1) G s1 s2 a
  | Put s k => fun G s1 s2 a => interp k G s s2 a (* s1 is discarded and replaced by s *)
  | Ask k => fun G s1 s2 a => interp (k G) G s1 s2 a
  | RestrictGraph P k => fun G s1 s2 a => P /\ interp k G s1 s2 a
  | Ret v => fun G s1 s2 a => s1 = s2 /\ a = v
  | HaltThread => fun G s1 s2 a => s1 = s2
  end.

Definition getReg(regs: Array Register word)(reg: Z): word :=
  if Z.eq_dec reg 0 then word.of_Z 0 else select regs reg.

Definition setReg(regs: Array Register word)(reg: Z)(v: word): Array Register word :=
  if Z.eq_dec reg Register0 then regs else store regs reg v.

Definition loadInstruction(a: word): M Instruction := s <- get; Return (IInstruction (select s.(Prog) a)).

(* load_byte and store_byte do everything that GEN from the paper does except the
   {addr,data,ctrl} assertions in the for loop, because for these, we need to know
   the register names, so we move these assertions into preExec *)
Definition load_byte(addr: word): M w8 :=
  s <- get;
  G <- ask;
  assert_graph (select G.(Lab) s.(CurrentEvent) = ReadLabel addr /\
                Typ G (select (Rf G) s.(CurrentEvent)) = WriteEvent);;
  let v := Val G (select (Rf G) s.(CurrentEvent)) in
  put (withCurrentEvent (NextEvent s.(CurrentEvent)) s);;
  Return v.
  (* Note: invalid memory accesses (such as array out of bounds) are not rejected here,
     but just recorded as constraints on the graph, and program correctness proofs will
     have to prove that all accesses in the graph are within the desired memory address range *)

Definition store_byte(addr: word)(v: w8): M unit :=
  s <- get;
  G <- ask;
  assert_graph (select G.(Lab) s.(CurrentEvent) = WriteLabel addr v);;
  put (withCurrentEvent (NextEvent s.(CurrentEvent)) s).

(* only 1-byte loads and stores are supported at the moment *)
Definition loadData(n: nat)(a: word): M (HList.tuple byte n) :=
  match n with
  | 1 => load_byte a
  | _ => reject_program
  end.

Definition storeData(n: nat)(a: word): HList.tuple byte n -> M unit :=
  match n with
  | 1 => store_byte a
  | _ => fun _ => reject_program
  end.

Definition loadN(n: nat)(kind: SourceType)(a: word): M (HList.tuple byte n) :=
  match kind with
  | Fetch => reject_program (* instructions are loaded directly, not through loadWord *)
  | Execute => loadData n a
  | VirtualMemory => reject_program
  end.

Definition storeN(n: nat)(kind: SourceType)(a: word)(v: HList.tuple byte n): M unit :=
  s <- get;
  match kind with
  | Fetch => reject_program
  | Execute => storeData n a v
  | VirtualMemory => reject_program
  end.

Definition minusone: Z := -1.
Definition pc: Register := minusone.

Definition emptyEvents: set Event := mkArray (fun _ => False).
Definition emptyDeps: Array Register (set Event) := mkArray (fun _ => emptyEvents).
Definition union{U: Type}(s1 s2: set U) :=
  mkArray (fun x => Array2Fun s1 x \/ Array2Fun s2 x).

Definition getDeps(D: Array Register (set Event))(r: Register): set Event :=
  if Z.eqb r 0 then emptyEvents else select D r.

Definition setDeps(D: Array Register (set Event))(r: Register)(s: set Event): Array Register (set Event) :=
  if Z.eqb r 0 then D else store D r s.

Notation "D <[ r ]>" := (getDeps D r)
  (at level 8, left associativity, only parsing).
Notation "D <[ r := s ]>" := (setDeps D r s)
  (at level 8, left associativity, only parsing).

Definition checkDepsI(inst: InstructionI): M unit :=
  match inst with
  (* only loading/storing one byte at a time is supported, the others will fail in load/storeData *)
  | Lb rd rs1 oimm12 => s <- get; G <- ask; assert_graph (
       select G.(Addr) s.(CurrentEvent) = s.(Deps)<[rs1]> /\
       select G.(Data) s.(CurrentEvent) = emptyEvents /\
       select G.(Ctrl) s.(CurrentEvent) = s.(Deps)<[pc]>
    )
  | Sb rs1 rs2 simm12 => s <- get; G <- ask; assert_graph (
       select G.(Addr) s.(CurrentEvent) = s.(Deps)<[rs1]> /\
       select G.(Data) s.(CurrentEvent) = s.(Deps)<[rs2]> /\
       select G.(Ctrl) s.(CurrentEvent) = s.(Deps)<[pc]>
    )
  (* instructions other than load/store need no dependency checking *)
  | _ => Return tt
  end.

Definition checkDeps(inst: Instruction): M unit :=
  match inst with
  | IInstruction i => checkDepsI i
  | _ => reject_program (* only I is supported at the moment *)
  end.

Definition updateDepsI(inst: InstructionI)(D: Array Register (set Event)): Array Register (set Event) :=
  match inst with
  | Lui rd imm20 => D
  (* QUESTION: here, and in jump instructions, control dependencies become data dependencies? *)
  | Auipc rd oimm20 => D<[rd := D<[pc]>]>
  (* Note: dependencies of pc remain unchanged because a constant is added *)
  | Jal rd jimm20 => D<[rd := D<[pc]>]>
  | Jalr rd rs1 oimm12 => D<[rd := D<[pc]>]><[pc := union D<[pc]> D<[rs1]>]>
  | Beq  rs1 rs2 sbimm12
  | Bne  rs1 rs2 sbimm12
  | Blt  rs1 rs2 sbimm12
  | Bge  rs1 rs2 sbimm12
  | Bltu rs1 rs2 sbimm12
  | Bgeu rs1 rs2 sbimm12 => D<[pc := union D<[pc]> (union D<[rs1]> D<[rs2]>)]>
  | Lb  rd rs1 oimm12
  | Lh  rd rs1 oimm12
  | Lw  rd rs1 oimm12
  | Lbu rd rs1 oimm12
  | Lhu rd rs1 oimm12 => D (* Note: D<[rd := {event from which value was read}]> was already done in loadN *)
  | Sb rs1 rs2 simm12
  | Sh rs1 rs2 simm12
  | Sw rs1 rs2 simm12 => D
  | Addi  rd rs1 _
  | Slti  rd rs1 _
  | Sltiu rd rs1 _
  | Xori  rd rs1 _
  | Ori   rd rs1 _
  | Andi  rd rs1 _
  | Slli  rd rs1 _
  | Srli  rd rs1 _
  | Srai  rd rs1 _ => D<[rd := D<[rs1]>]>
  | Add  rd rs1 rs2
  | Sub  rd rs1 rs2
  | Sll  rd rs1 rs2
  | Slt  rd rs1 rs2
  | Sltu rd rs1 rs2
  | Xor  rd rs1 rs2
  | Or   rd rs1 rs2
  | Srl  rd rs1 rs2
  | Sra  rd rs1 rs2
  | And  rd rs1 rs2 => D<[rd := union D<[rs1]> D<[rs2]>]>
  | Fence pred succ => D (* QUESTION: any dependencies here? *)
  | Fence_i => D
  | InvalidI => D
  end.

Definition updateDeps(inst: Instruction): Array Register (set Event) -> Array Register (set Event) :=
  match inst with
  | IInstruction i => updateDepsI i
  | _ => id (* only I is supported at the moment *)
  end.

#[global] Instance IsRiscvMachine: RiscvProgram M word :=  {
  getRegister reg := s <- get; Return (getReg s.(Regs) reg);
  setRegister reg v := s <- get; put (withRegs (setReg s.(Regs) reg v) s);
  getPC := s <- get; Return s.(Pc);
  setPC newPc := s <- get; put (withNextPc newPc s);

  loadByte   := loadN 1;
  loadHalf   := loadN 2;
  loadWord   := loadN 4;
  loadDouble := loadN 8;

  storeByte   := storeN 1;
  storeHalf   := storeN 2;
  storeWord   := storeN 4;
  storeDouble := storeN 8;

  (* atomics, CSRs, and non-machine modes are not supported *)
  makeReservation  addr := reject_program;
  clearReservation addr := reject_program;
  checkReservation addr := reject_program;
  getCSRField f := reject_program;
  setCSRField f v := reject_program;
  getPrivMode := reject_program;
  setPrivMode v := reject_program;

  fence a b := (* TODO honor arguments of fence *)
    s <- get;
    G <- ask;
    assert_graph (select G.(Lab) s.(CurrentEvent) = FenceLabel);;
    put (withCurrentEvent (NextEvent s.(CurrentEvent)) s);

  endCycleNormal := s <- get; put (withPc s.(NextPc) (withNextPc (word.add s.(NextPc) (word.of_Z 4)) s));

  (* exceptions are not supported *)
  endCycleEarly{A: Type} := reject_program;
}.

Definition post_execute(inst: Instruction): M unit :=
  s <- get; put (withDeps (updateDeps inst s.(Deps)) s).

Definition pre_execute(inst: Instruction): M unit := checkDeps inst.

Definition run1: M unit :=
  pc <- getPC;
  inst <- loadInstruction pc;
  pre_execute inst;;
  execute inst;;
  post_execute inst;;
  endCycleNormal.

(* Note: this only works as long as we don't use endCycleEarly, because otherwise
   all the remaining cycles (instead of just all the remaining operations *within*
   the current cycle) are skipped. *)
Definition runN(n: nat): M unit := power_func (fun m => run1;; m) n (Return tt).

Definition initialRegs: Array Register word := mkArray (fun _ => word.of_Z 0).

Fixpoint prog2Array(l: list InstructionI)(start: word): Array word InstructionI :=
  match l with
  | nil => constArray word InstructionI InvalidI
  | i :: rest => store (prog2Array rest (word.add start (word.of_Z 4))) start i
  end.

Definition initialState(id: Tid)(prog: list InstructionI): ThreadState := {|
  Regs := initialRegs;
  Pc := word.of_Z 0;
  NextPc := word.of_Z 4;
  Prog := prog2Array prog (word.of_Z 0);
  CurrentEvent := ThreadEvent id 0;
  Deps := emptyDeps
|}.

Ltac inv H := inversion H; clear H; subst.

Require Import riscv.Utility.InstructionCoercions. Open Scope ilist_scope.
Require Import riscv.Utility.RegisterNames.
Require Import riscv.Spec.PseudoInstructions.

(* s1 := s0 by making a detour throug memory *)
Definition readAfterWriteProg := [
  Sb a0 s0 0;
  Lb s1 a0 0
].

(* register a0 contains the address of the one-element FIFO,
   register a1 contains the address of the isEmpty flag,
   register s0 contains the value to be put into the FIFO *)
Definition writerProg := [
  Sb a0 s0 0;   (* store the value into the FIFO *)
  Sb a1 zero 0  (* set the isEmpty flag to false *)
].

Definition readerProg := [
  Lb t0 a1 0;   (* start: t0 := isEmpty *)
  Beqz t0 (-4); (* if (isEmpty) { goto start } *)
  Lb s0 a0 0    (* read value from FIFO *)
].

(* TODO more setup/preconditions on initial state will be needed (a0, a1) *)
Definition initialReaderState := initialState 0%nat readerProg.
Definition initialWriterState := initialState 1%nat writerProg.

Ltac simpl_exec :=
  cbn -[w8 w32 word map.empty word.of_Z word.unsigned word.and word.add getReg map.put initialRegs] in *.

Lemma remove_exists_unit_iff: forall (P: Prop),
    (exists _: unit, P) <-> P.
Proof. split; intros. 1: destruct H. 2: exists tt. all: assumption. Qed.

Lemma remove_exists_unit: forall (P: Prop),
    (exists _: unit, P) = P.
Proof. intros. apply propositional_extensionality. apply remove_exists_unit_iff. Qed.

Ltac step :=
  match goal with
  | |- _ => progress cbv delta [withRegs withPc withNextPc withProg withCurrentEvent withDeps]
  | |- _ => rewrite !remove_exists_unit
  | |- context [@nth_error ?A ?l ?i] =>
    progress let r := eval cbv in i in change i with r
  | |- context [decode ?iset (LittleEndian.combine 4 (LittleEndian.split 4 ?v))] =>
    lazymatch isZcst v with
    | true => idtac
    end;
    progress let r := eval cbv in
             (decode iset (LittleEndian.combine 4 (LittleEndian.split 4 v))) in
      change (decode iset (LittleEndian.combine 4 (LittleEndian.split 4 v))) with r
  | |- _ => progress simpl_exec
  end.

Derive InstructionI_matching
  SuchThat (forall inst: InstructionI, InstructionI_matching inst = True)
  As InstructionI_matching_correct.
Proof.
  intros.
  symmetry.
  etransitivity. {
    instantiate (1 := ltac:(destruct inst)).
Abort.

Derive simplified_run1
  SuchThat (forall G s1 s2, simplified_run1 G s1 s2 =
                            interp run1 G s1 s2 tt)
  As run1_correct.
Proof.
  intros.
  unfold run1, loadInstruction, pre_execute, execute, post_execute, checkDeps, checkDepsI,
    updateDeps, updateDepsI, ExecuteI.execute, pc.
  symmetry.
  cbn [getPC IsRiscvMachine bind Return Bind M_Monad get interp].
  etransitivity. {
    instantiate (1 := ltac:(destruct (select (Prog s1) (Pc s1)))).
    destruct (select (Prog s1) (Pc s1)).
    all: cbn -[minusone w8 w32 word map.empty word.of_Z word.unsigned word.and word.add getReg map.put initialRegs].
    all: try lazymatch goal with
         | |- interp ?M _ _ _ _ = _ => fail
         | |- _ => reflexivity
         end.
    all: unfold when.
    all: match goal with
         | |- interp (bind (if ?B then _ else _) _) _ _ _ _ = _ =>
           instantiate (1 := ltac:(destruct B)); destruct B
         end.
    all: cbn -[minusone w8 w32 word map.empty word.of_Z word.unsigned word.and word.add getReg map.put initialRegs].
    all: try lazymatch goal with
         | |- interp ?M _ _ _ _ = _ => fail
         | |- _ => reflexivity
         end.
    all: match goal with
         | |- interp (bind (if ?B then _ else _) _) _ _ _ _ = _ =>
           instantiate (1 := ltac:(destruct B)); destruct B
         end.
    all: cbn -[minusone w8 w32 word map.empty word.of_Z word.unsigned word.and word.add getReg map.put initialRegs].
    all: try lazymatch goal with
         | |- interp ?M _ _ _ _ = _ => fail
         | |- _ => reflexivity
         end.
  }
  cbn -[minusone w8 w32 word map.empty word.of_Z word.unsigned word.and word.add getReg map.put initialRegs].
  subst simplified_run1.
  reflexivity.
Qed.

(*
Print simplified_run1.
*)

Local Set Warnings "-notation-both-format-and-spaces".

Notation "(_ 'bv2nat' 32) A" := (word.unsigned A) (at level 10, A at level 0, only printing).
Notation "(_ 'int2bv' 32) A" := (word.of_Z A) (at level 10, A at level 0, only printing).
Notation "'bvadd' A B" := (word.add A B) (at level 10, A at level 0, B at level 0).
Notation "'bvsub' A B" := (word.sub A B) (at level 10, A at level 0, B at level 0).
Notation "'bvneg' A" := (word.opp A) (at level 10, A at level 0).
Notation "'bvor' A B" := (word.or A B) (at level 10, A at level 0, B at level 0).
Notation "'bvand' A B" := (word.and A B) (at level 10, A at level 0, B at level 0).
Notation "'bvxor' A B" := (word.xor A B) (at level 10, A at level 0, B at level 0).
Notation "'bvnot' A" := (word.not A) (at level 10, A at level 0).
Notation "'bvmul' A B" := (word.mul A B) (at level 10, A at level 0, B at level 0).
Notation "'bvurem' A B" := (word.modu A B) (at level 10, A at level 0, B at level 0).
Notation "'bvshl' A B" := (word.slu A B) (at level 10, A at level 0, B at level 0).
Notation "'bvlshr' A B" := (word.sru A B) (at level 10, A at level 0, B at level 0).
Notation "'bvashr' A B" := (word.srs A B) (at level 10, A at level 0, B at level 0).
Notation "= A B" := (word.eqb A B) (at level 10, A at level 0, B at level 0).
Notation "'bvult' A B" := (word.ltu A B) (at level 10, A at level 0, B at level 0).
Notation "'bvslt' A B" := (word.lts A B) (at level 10, A at level 0, B at level 0).

Notation "(_ 'sign_extend' 24) A" := (word.of_Z (signExtend 8 (LittleEndian.combine 1 A)))
  (at level 10, A at level 0, only printing).
Notation "(_ 'zero_extend' 24) A" := (word.of_Z (LittleEndian.combine 1 A))
  (at level 10, A at level 0, only printing).
Notation "(_ 'extract' 7 0) A" := (LittleEndian.split 1 (word.unsigned A))
  (at level 10, A at level 0, only printing).


Notation "'(match'  inst ( ( '(Lb'  rd_Lb rs1_Lb oimm12_Lb ) branchLb ) ( '(Lh'  rd_Lh rs1_Lh oimm12_Lh ) branchLh ) ( '(Lw'  rd_Lw rs1_Lw oimm12_Lw ) branchLw ) ( '(Lbu'  rd_Lbu rs1_Lbu oimm12_Lbu ) branchLbu ) ( '(Lhu'  rd_Lhu rs1_Lhu oimm12_Lhu ) branchLhu ) ( '(Fence'  pred_Fence succ_Fence ) branchFence ) ( '(Fence_i'  ) branchFence_i ) ( '(Addi'  rd_Addi rs1_Addi imm12_Addi ) branchAddi ) ( '(Slli'  rd_Slli rs1_Slli shamt6_Slli ) branchSlli ) ( '(Slti'  rd_Slti rs1_Slti imm12_Slti ) branchSlti ) ( '(Sltiu'  rd_Sltiu rs1_Sltiu imm12_Sltiu ) branchSltiu ) ( '(Xori'  rd_Xori rs1_Xori imm12_Xori ) branchXori ) ( '(Ori'  rd_Ori rs1_Ori imm12_Ori ) branchOri ) ( '(Andi'  rd_Andi rs1_Andi imm12_Andi ) branchAndi ) ( '(Srli'  rd_Srli rs1_Srli shamt6_Srli ) branchSrli ) ( '(Srai'  rd_Srai rs1_Srai shamt6_Srai ) branchSrai ) ( '(Auipc'  rd_Auipc oimm20_Auipc ) branchAuipc ) ( '(Sb'  rs1_Sb rs2_Sb simm12_Sb ) branchSb ) ( '(Sh'  rs1_Sh rs2_Sh simm12_Sh ) branchSh ) ( '(Sw'  rs1_Sw rs2_Sw simm12_Sw ) branchSw ) ( '(Add'  rd_Add rs1_Add rs2_Add ) branchAdd ) ( '(Sub'  rd_Sub rs1_Sub rs2_Sub ) branchSub ) ( '(Sll'  rd_Sll rs1_Sll rs2_Sll ) branchSll ) ( '(Slt'  rd_Slt rs1_Slt rs2_Slt ) branchSlt ) ( '(Sltu'  rd_Sltu rs1_Sltu rs2_Sltu ) branchSltu ) ( '(Xor'  rd_Xor rs1_Xor rs2_Xor ) branchXor ) ( '(Srl'  rd_Srl rs1_Srl rs2_Srl ) branchSrl ) ( '(Sra'  rd_Sra rs1_Sra rs2_Sra ) branchSra ) ( '(Or'  rd_Or rs1_Or rs2_Or ) branchOr ) ( '(And'  rd_And rs1_And rs2_And ) branchAnd ) ( '(Lui'  rd_Lui imm20_Lui ) branchLui ) ( '(Beq'  rs1_Beq rs2_Beq sbimm12_Beq ) branchBeq ) ( '(Bne'  rs1_Bne rs2_Bne sbimm12_Bne ) branchBne ) ( '(Blt'  rs1_Blt rs2_Blt sbimm12_Blt ) branchBlt ) ( '(Bge'  rs1_Bge rs2_Bge sbimm12_Bge ) branchBge ) ( '(Bltu'  rs1_Bltu rs2_Bltu sbimm12_Bltu ) branchBltu ) ( '(Bgeu'  rs1_Bgeu rs2_Bgeu sbimm12_Bgeu ) branchBgeu ) ( '(Jalr'  rd_Jalr rs1_Jalr oimm12_Jalr ) branchJalr ) ( '(Jal'  rd_Jal jimm20_Jal ) branchJal ) ( '(InvalidI'  ) branchInvalidI )))"

:= match inst with
   | Lb rd_Lb rs1_Lb oimm12_Lb => branchLb
   | Lh rd_Lh rs1_Lh oimm12_Lh => branchLh
   | Lw rd_Lw rs1_Lw oimm12_Lw => branchLw
   | Lbu rd_Lbu rs1_Lbu oimm12_Lbu => branchLbu
   | Lhu rd_Lhu rs1_Lhu oimm12_Lhu => branchLhu
   | Fence pred_Fence succ_Fence => branchFence
   | Fence_i => branchFence_i
   | Addi rd_Addi rs1_Addi imm12_Addi => branchAddi
   | Slli rd_Slli rs1_Slli shamt6_Slli => branchSlli
   | Slti rd_Slti rs1_Slti imm12_Slti => branchSlti
   | Sltiu rd_Sltiu rs1_Sltiu imm12_Sltiu => branchSltiu
   | Xori rd_Xori rs1_Xori imm12_Xori => branchXori
   | Ori rd_Ori rs1_Ori imm12_Ori => branchOri
   | Andi rd_Andi rs1_Andi imm12_Andi => branchAndi
   | Srli rd_Srli rs1_Srli shamt6_Srli => branchSrli
   | Srai rd_Srai rs1_Srai shamt6_Srai => branchSrai
   | Auipc rd_Auipc oimm20_Auipc => branchAuipc
   | Sb rs1_Sb rs2_Sb simm12_Sb => branchSb
   | Sh rs1_Sh rs2_Sh simm12_Sh => branchSh
   | Sw rs1_Sw rs2_Sw simm12_Sw => branchSw
   | Add rd_Add rs1_Add rs2_Add => branchAdd
   | Sub rd_Sub rs1_Sub rs2_Sub => branchSub
   | Sll rd_Sll rs1_Sll rs2_Sll => branchSll
   | Slt rd_Slt rs1_Slt rs2_Slt => branchSlt
   | Sltu rd_Sltu rs1_Sltu rs2_Sltu => branchSltu
   | Xor rd_Xor rs1_Xor rs2_Xor => branchXor
   | Srl rd_Srl rs1_Srl rs2_Srl => branchSrl
   | Sra rd_Sra rs1_Sra rs2_Sra => branchSra
   | Or rd_Or rs1_Or rs2_Or => branchOr
   | And rd_And rs1_And rs2_And => branchAnd
   | Lui rd_Lui imm20_Lui => branchLui
   | Beq rs1_Beq rs2_Beq sbimm12_Beq => branchBeq
   | Bne rs1_Bne rs2_Bne sbimm12_Bne => branchBne
   | Blt rs1_Blt rs2_Blt sbimm12_Blt => branchBlt
   | Bge rs1_Bge rs2_Bge sbimm12_Bge => branchBge
   | Bltu rs1_Bltu rs2_Bltu sbimm12_Bltu => branchBltu
   | Bgeu rs1_Bgeu rs2_Bgeu sbimm12_Bgeu => branchBgeu
   | Jalr rd_Jalr rs1_Jalr oimm12_Jalr => branchJalr
   | Jal rd_Jal jimm20_Jal => branchJal
   | InvalidI => branchInvalidI
   end

(at level 10,
   inst at level 0,
   branchLb at level 0,
   branchLh at level 0,
   branchLw at level 0,
   branchLbu at level 0,
   branchLhu at level 0,
   branchFence at level 0,
   branchFence_i at level 0,
   branchAddi at level 0,
   branchSlli at level 0,
   branchSlti at level 0,
   branchSltiu at level 0,
   branchXori at level 0,
   branchOri at level 0,
   branchAndi at level 0,
   branchSrli at level 0,
   branchSrai at level 0,
   branchAuipc at level 0,
   branchSb at level 0,
   branchSh at level 0,
   branchSw at level 0,
   branchAdd at level 0,
   branchSub at level 0,
   branchSll at level 0,
   branchSlt at level 0,
   branchSltu at level 0,
   branchXor at level 0,
   branchSrl at level 0,
   branchSra at level 0,
   branchOr at level 0,
   branchAnd at level 0,
   branchLui at level 0,
   branchBeq at level 0,
   branchBne at level 0,
   branchBlt at level 0,
   branchBge at level 0,
   branchBltu at level 0,
   branchBgeu at level 0,
   branchJalr at level 0,
   branchJal at level 0,
   branchInvalidI at level 0,

format "'(match'  inst  ( '//' ( '(Lb'  rd_Lb  rs1_Lb  oimm12_Lb )  branchLb ) '//' ( '(Lh'  rd_Lh  rs1_Lh  oimm12_Lh )  branchLh ) '//' ( '(Lw'  rd_Lw  rs1_Lw  oimm12_Lw )  branchLw ) '//' ( '(Lbu'  rd_Lbu  rs1_Lbu  oimm12_Lbu )  branchLbu ) '//' ( '(Lhu'  rd_Lhu  rs1_Lhu  oimm12_Lhu )  branchLhu ) '//' ( '(Fence'  pred_Fence  succ_Fence )  branchFence ) '//' ( '(Fence_i' )  branchFence_i ) '//' ( '(Addi'  rd_Addi  rs1_Addi  imm12_Addi )  branchAddi ) '//' ( '(Slli'  rd_Slli  rs1_Slli  shamt6_Slli )  branchSlli ) '//' ( '(Slti'  rd_Slti  rs1_Slti  imm12_Slti )  branchSlti ) '//' ( '(Sltiu'  rd_Sltiu  rs1_Sltiu  imm12_Sltiu )  branchSltiu ) '//' ( '(Xori'  rd_Xori  rs1_Xori  imm12_Xori )  branchXori ) '//' ( '(Ori'  rd_Ori  rs1_Ori  imm12_Ori )  branchOri ) '//' ( '(Andi'  rd_Andi  rs1_Andi  imm12_Andi )  branchAndi ) '//' ( '(Srli'  rd_Srli  rs1_Srli  shamt6_Srli )  branchSrli ) '//' ( '(Srai'  rd_Srai  rs1_Srai  shamt6_Srai )  branchSrai ) '//' ( '(Auipc'  rd_Auipc  oimm20_Auipc )  branchAuipc ) '//' ( '(Sb'  rs1_Sb  rs2_Sb  simm12_Sb )  branchSb ) '//' ( '(Sh'  rs1_Sh  rs2_Sh  simm12_Sh )  branchSh ) '//' ( '(Sw'  rs1_Sw  rs2_Sw  simm12_Sw )  branchSw ) '//' ( '(Add'  rd_Add  rs1_Add  rs2_Add )  branchAdd ) '//' ( '(Sub'  rd_Sub  rs1_Sub  rs2_Sub )  branchSub ) '//' ( '(Sll'  rd_Sll  rs1_Sll  rs2_Sll )  branchSll ) '//' ( '(Slt'  rd_Slt  rs1_Slt  rs2_Slt )  branchSlt ) '//' ( '(Sltu'  rd_Sltu  rs1_Sltu  rs2_Sltu )  branchSltu ) '//' ( '(Xor'  rd_Xor  rs1_Xor  rs2_Xor )  branchXor ) '//' ( '(Srl'  rd_Srl  rs1_Srl  rs2_Srl )  branchSrl ) '//' ( '(Sra'  rd_Sra  rs1_Sra  rs2_Sra )  branchSra ) '//' ( '(Or'  rd_Or  rs1_Or  rs2_Or )  branchOr ) '//' ( '(And'  rd_And  rs1_And  rs2_And )  branchAnd ) '//' ( '(Lui'  rd_Lui  imm20_Lui )  branchLui ) '//' ( '(Beq'  rs1_Beq  rs2_Beq  sbimm12_Beq )  branchBeq ) '//' ( '(Bne'  rs1_Bne  rs2_Bne  sbimm12_Bne )  branchBne ) '//' ( '(Blt'  rs1_Blt  rs2_Blt  sbimm12_Blt )  branchBlt ) '//' ( '(Bge'  rs1_Bge  rs2_Bge  sbimm12_Bge )  branchBge ) '//' ( '(Bltu'  rs1_Bltu  rs2_Bltu  sbimm12_Bltu )  branchBltu ) '//' ( '(Bgeu'  rs1_Bgeu  rs2_Bgeu  sbimm12_Bgeu )  branchBgeu ) '//' ( '(Jalr'  rd_Jalr  rs1_Jalr  oimm12_Jalr )  branchJalr ) '//' ( '(Jal'  rd_Jal  jimm20_Jal )  branchJal ) '//' ( '(InvalidI' )  branchInvalidI )))").


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

Notation "'as'  'None'  '(option'  T )" := (@None T) (at level 10, T at level 0).

(* Print simplified_run1. *)

Goal forall G s1 s2, simplified_run1 G s1 s2 = True.
Proof.
  intros.
  unfold simplified_run1.

  (* using match_marker and InstructionI_elim, we might be able to create a notation for
     match, but how can we get the constructor names for the branches? *)
Abort.

Derive readAfterWriteGraphConditions
  SuchThat (forall G final, readAfterWriteGraphConditions G final =
                            interp (runN 2) G (initialState 0%nat readAfterWriteProg) final tt)
  As readAfterWriteGraphConditions_correct.
Proof.
  intros.
  unfold initialState, readAfterWriteProg.
  repeat step.
  subst readAfterWriteGraphConditions.
  reflexivity.
Defined.

Derive writerGraphConditions
  SuchThat (forall G final, writerGraphConditions G final =
                            interp (runN 2) G initialWriterState final tt)
  As writerGraphConditions_correct.
Proof.
  intros. unfold initialWriterState, initialState, writerProg.
  repeat step.
  subst writerGraphConditions.
  reflexivity.
Defined.

Derive readerGraphConditions
  SuchThat (forall G final, readerGraphConditions G final =
                            interp (runN 2) G initialReaderState final tt)
  As readerGraphConditions_correct.
Proof.
  intros. unfold initialReaderState, initialState, readerProg.
  repeat step.
  unfold when in *.
  (* need to push bind into branches of if *)
Abort.

(*
(* ensures codomains of functions are correct etc *)
Record Wf(G: Graph) := mkWf {
  WfRfWrite: forall e, Rf G e \in WriteEvents G;
  WfLabInit: forall x, Lab G (InitEvent x) = None \/
                       exists v, Lab G (InitEvent x) = Some (WriteLabel x v);
  WfRfLocMatches: forall e, Loc G (Rf G e) = Loc G e;
}.

Lemma mo_implies_po_within_same_thread: forall {G thr iid1 iid2 mo},
    modificationOrder G mo ->
    SC_acyclicity G mo ->
    mo (ThreadEvent thr iid1) (ThreadEvent thr iid2) ->
    (iid1 < iid2)%nat.
Proof.
  intros *. intros [ MOStrict [MOWrite MODec] ] Ac Comp.
  assert (iid1 < iid2 \/ iid1 = iid2 \/ iid2 < iid1)%nat as A by blia.
  destruct A as [ A | [A | A] ].
  - assumption.
  - subst. exfalso. eapply strictPartialOrder_irreflexive; eassumption.
  - exfalso. unfold SC_acyclicity, acyclic, hasCycle in Ac.
    apply Ac.
    exists (ThreadEvent thr iid1).
    unfold unionrel.
    eapply TrclCons with (a2 := ThreadEvent thr iid2).
    2: eapply TrclOne.
    all: cbn.
    all: auto.
Qed.

Lemma rf_implies_po_within_same_thread: forall {G thr iid1 iid2 mo},
    modificationOrder G mo ->
    SC_acyclicity G mo ->
    RfRel G (ThreadEvent thr iid1) (ThreadEvent thr iid2) ->
    (iid1 < iid2)%nat.
Proof.
  intros *. intros [ MOStrict [MOWrite MODec] ] Ac R.
  unfold SC_acyclicity, acyclic, hasCycle in Ac.
  assert (iid1 < iid2 \/ iid1 = iid2 \/ iid2 < iid1)%nat as A by blia.
  destruct A as [ A | [A | A] ].
  - assumption.
  - subst. exfalso. apply Ac. exists (ThreadEvent thr iid2).
    unfold unionrel. apply TrclOne. auto.
  - subst. exfalso. apply Ac. exists (ThreadEvent thr iid1).
    unfold unionrel.
    eapply TrclCons with (a2 := ThreadEvent thr iid2).
    2: eapply TrclOne.
    all: cbn.
    all: auto.
Qed.

Lemma ownedReadAfterWrite: forall G iid1 iid2 thr loc val,
    Wf G ->
    consSC G ->
    (iid1 < iid2)%nat ->
    Lab G (ThreadEvent thr iid1) = Some (WriteLabel loc val) ->
    Lab G (ThreadEvent thr iid2) = Some (ReadLabel loc) ->
    (* between (ThreadEvent thr iid1) and (ThreadEvent thr iid2), only reads happened at this location *)
    (forall e, e \in ThreadEvents G -> Loc G e = Loc G (ThreadEvent thr iid2) ->
               po (ThreadEvent thr iid1) e -> po e (ThreadEvent thr iid2) -> Typ G e = ReadEvent) ->
    (* the current thread owns this location, ie. no other thread ever accesses it *)
    (forall e, e \in ThreadEvents G -> Loc G e = Loc G (ThreadEvent thr iid2) -> tid e = thr) ->
    Rf G (ThreadEvent thr iid2) = (ThreadEvent thr iid1).
Proof.
  intros *. intros W Co Iidlt L1 L2 TyR Th. intros. unfold PropSet.elem_of in *.
  destruct (Rf G (ThreadEvent thr iid2)) as [x|thr' iid1'] eqn: E.
  1: case (@TODO False). (* init event case *)
  assert (Rf G (ThreadEvent thr iid2) \in ThreadEvents G) as I1 by case (@TODO False). unfold elem_of in I1.
  pose proof (WfRfLocMatches G W (ThreadEvent thr iid2)) as I2.
  rewrite E in I1, I2.
  specialize (Th _ I1 I2). simpl in Th. subst thr'.
  f_equal.
  unfold consSC in *. destruct Co as [mo [MO AC] ].
  unfold acyclic, hasCycle in AC.
  pose proof MO as MO'.
  destruct MO' as [MOStrict [MOWrite MODec] ].
  specialize (MODec (ThreadEvent thr iid1) (ThreadEvent thr iid1')).
  pose proof (WfRfWrite G W (ThreadEvent thr iid2)) as A1.
  rewrite E in A1. specialize MODec with (2 := A1). clear A1.
  unfold elem_of, WriteEvents in MODec.
  rewrite L1 in MODec.
  exfalso. apply AC.
  assert (RfRel G (ThreadEvent thr iid1') (ThreadEvent thr iid2)). {
    rewrite <- E. constructor. unfold ReadEvents, elem_of. eauto.
  }
  destruct MODec as [MODec | MODec]. 1: clear; eauto.
  - (* case 1: the fake iid' is after iid1. Contradicts assumption that only read-events are
     between iid1 and iid2 *)
    exfalso.
    specialize (TyR (ThreadEvent thr iid1') I1 I2).
    simpl in TyR.
    specialize MOWrite with (1 := MODec). simp.
    rewrite MOWritep1 in TyR.
    eenough _.
    2: eapply TyR. 1: discriminate.
    all: eauto using mo_implies_po_within_same_thread, rf_implies_po_within_same_thread.
  - (* case 2: the fake iid' is before iid1: Contradicts SC_acyclicity *)
    unfold hasCycle.
    exists (ThreadEvent thr iid1).
    unfold unionrel, invrel, composerel.
    eapply TrclCons with (a2 := ThreadEvent thr iid2).
    2: eapply TrclOne.
    all: cbn.
    all: eauto.
Qed.

(* the end of an execution is reached when the pc points one past the last instruction
   in the list of instructions *)
Inductive runToEnd(G: Graph): ThreadState -> ThreadState -> Prop :=
| RDone: forall s,
    Z.to_nat (word.unsigned s.(Pc) / 4) = length s.(Prog) ->
    runToEnd G s s
| RStep: forall s1 s2 s3,
    interp run1 G s1 s2 tt ->
    runToEnd G s2 s3 ->
    runToEnd G s1 s3.

Lemma readAfterWriteWorks: forall G final,
    errorFree G ->
    Wf G ->
    consSC G ->
    runToEnd G (initialState 0%nat readAfterWriteProg) final ->
    word.and (getReg final.(Regs) s1) (word.of_Z 255) =
    word.and (getReg final.(Regs) s0) (word.of_Z 255).
Proof.
  unfold initialState, s0, s1. intros *. intros EF W. intros.

  (* Sb a0 s0 0 *)
  inv H0. 1: discriminate H1.
  unfold run1 in H1.
  simpl_exec.
  simp.
  unfold pre_execute, get, put in *.
  simp.
  subst.
  simpl_exec.
  simp.
  cbv in E.
  eassert (decode RV32I (LittleEndian.combine 4 w) = _) as A. {
    apply Option.eq_of_eq_Some in E. subst w. cbv. reflexivity.
  }
  rewrite A in *.
  clear E A w.
  simpl_exec.
  simp.
  unfold pre_execute, get, put, assert_graph, ask in *.
  simp.
  simpl_exec.

  (* Lb s1 a0 0 *)
  inv H2. 1: discriminate H0.
  unfold run1 in H0.
  simpl_exec.
  simp.
  unfold pre_execute, get, put in *.
  simp.
  subst.
  simpl_exec.
  simp.
  cbv in E.
  eassert (decode RV32I (LittleEndian.combine 4 w) = _) as A. {
    apply Option.eq_of_eq_Some in E. subst w. cbv. reflexivity.
  }
  rewrite A in *.
  clear E A w.
  simpl_exec.
  simp.
  unfold pre_execute, get, put, assert_graph, ask in *.
  simp.
  simpl_exec.
  simp.
  subst.
  simpl_exec.
  cbv delta [RecordSet.set] in H1.
  simpl_exec.

  inv H1. 2: {
    (* running one more instruction is contradictory *)
    unfold run1 in H0.
    simpl_exec.
    simp.
    unfold pre_execute, get, put in *.
    simp.
(*
    discriminate E0.
  }

  cbv in H0. clear H0.
  simpl_exec.

  (* memory model business starts *)
  rename a9 into G.
  replace (Rf G (ThreadEvent 0%nat 1)) with (ThreadEvent 0%nat 0) in *. 2: {
    symmetry. eapply ownedReadAfterWrite; try eassumption.
    - cbv. reflexivity.
    - intros. unfold po in *. destruct e; try contradiction. simp. blia.
    - case (@TODO False). (* ownership of this location needs to become a hypothesis *)
  }
  unfold Val in *.
  match goal with
  | Hp: Lab G ?e = Some _ |- _ => rewrite Hp in *
  end.
  apply Option.eq_of_eq_Some in E. subst w.
  rewrite LittleEndian.combine_split.
  unfold getReg. simpl (Z.eq_dec 9 0). simpl (Z.eq_dec 8 0). cbv [id].
  rewrite map.get_put_same by reflexivity.
  rewrite map.get_put_diff by congruence.
  remember (match map.get initialRegs 8 with
            | Some x => x
            | None => word.of_Z 0
            end) as v0.
  rewrite signExtend_alt_bitwise by (reflexivity || assumption).
  match goal with
  | |- ?x = ?y => refine (@word.unsigned_inj _ _ _ x y _)
  end.
  rewrite !word.unsigned_and. unfold word.wrap.
  unfold signExtend_bitwise.
  remember (@word.unsigned 32 (Naive.word 32) v0) as V.
  clear.
  rewrite !word.unsigned_of_Z. unfold word.wrap.
  change (8 - 1) with 7.
  change (Z.of_nat 1 * 8) with 8.
  rewrite <- !Z.land_ones by discriminate.
  change 255 with (Z.ones 8).
  prove_Zeq_bitwise.
Time Qed. (* 20s *)
*)
Abort.

Lemma message_passing_works: forall G finalReaderState finalWriterState,
    consSC G ->
    runToEnd G initialReaderState finalReaderState ->
    runToEnd G initialWriterState finalWriterState ->
    getReg finalWriterState.(Regs) s0 = getReg initialWriterState.(Regs) s0.
Proof.
  intros *. intros Co RR RW.
  inv RW. 1: discriminate H.
  unfold run1, initialWriterState, initialState in H.
  simpl_exec.
  simp.
  simpl_exec.
  simp.
  unfold pre_execute, checkDeps in *.
  simp.
  unfold get in *.
  simp.
  simpl_exec.
  cbv in E.
  simp.
  (*
  cbv in E0.
  simp.
  simpl_exec.
  simp.
  unfold get in *.
  simp.
  unfold assert_graph, ask in *.
  simpl_exec.
  simp.
  simp.
  simpl_exec.
  simp.
  unfold put in *.
  subst.
  simpl_exec.
  cbv delta [RecordSet.set] in H0.
  simpl_exec.
  *)
Abort.

(* alternative: free monad based: *)
Definition run_primitive(a: riscv_primitive)(s: ThreadState)(G: Graph)(s': ThreadState):
  primitive_result a -> Prop :=
  match a with
  | GetRegister reg => TODO
  | SetRegister reg v => TODO
  | GetPC => TODO
  | SetPC newPC => TODO
  | LoadByte ctxid a => TODO
  | LoadHalf ctxid a => TODO
  | LoadWord ctxid a => TODO
  | LoadDouble ctxid a => TODO
  | StoreByte ctxid a v => TODO
  | StoreHalf ctxid a v => TODO
  | StoreWord ctxid a v => TODO
  | StoreDouble ctxid a v => TODO
  | EndCycleNormal => TODO
  | EndCycleEarly _ => TODO
  | GetCSRField f => TODO
  | SetCSRField f v => TODO
  | GetPrivMode => TODO
  | SetPrivMode mode => TODO
  | MakeReservation _
  | ClearReservation _
  | CheckReservation _
    => TODO
  end.
*)
