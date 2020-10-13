Require Import Coq.Lists.List. Import ListNotations.
Require Import coqutil.Tactics.Tactics.
Require Import coqutil.Tactics.Simp.
Require Import riscv.Spec.Decode.
Require Import riscv.Spec.Machine.
Require Import riscv.Spec.Execute.
Require Import riscv.Utility.Monads.
Require Import riscv.Utility.MonadNotations.
Require Import riscv.Utility.Utility.
Require Import riscv.Utility.Encode.
Require Import RecordUpdate.RecordUpdate.
Require Import coqutil.Z.Lia.
Require Import coqutil.Map.Interface.
Require Import riscv.Platform.MaterializeRiscvProgram.
Require Import riscv.Utility.Words32Naive.
Require Import coqutil.Map.Z_keyed_SortedListMap.
Require Import coqutil.Datatypes.PropSet.
Require Import coqutil.Map.OfFunc.
Require Import coqutil.Word.Properties.
Require Import coqutil.Z.prove_Zeq_bitwise.
Require Import Coq.ZArith.ZArith.

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
| ErrorLabel.

Inductive EventTyp := ReadEvent | WriteEvent | FenceEvent | ErrorEvent.

Definition LabelTyp(l: Label): EventTyp :=
  match l with
  | ReadLabel _ => ReadEvent
  | WriteLabel _ _ => WriteEvent
  | FenceLabel => FenceEvent
  | ErrorLabel => ErrorEvent
  end.

Record Graph := mkGraph {
  (* label of each event, None means the event is not part of the graph *)
  Lab: Event -> option Label;
  (* reads-from function: maps each read event to the write event of the same location
     that determines the read's value *)
  Rf: Event -> Event;
  (* address dependencies of memory accesses *)
  Addr: Event -> (set Event);
  (* data dependencies of writes *)
  Data: Event -> (set Event);
  (* control dependencies of events *)
  Ctrl: Event -> (set Event);
}.

Definition Events(G: Graph): set Event :=
  fun e => exists l, G.(Lab) e = Some l.

Definition InitializationEvents(G: Graph): set Event :=
  fun e => exists x v, e = InitEvent x /\ G.(Lab) e = Some (WriteLabel x v).

Definition ThreadEvents(G: Graph): set Event :=
  fun e => exists l t i, e = ThreadEvent t i /\ G.(Lab) e = Some l.

Definition ReadEvents(G: Graph): set Event :=
  fun e => exists x, G.(Lab) e = Some (ReadLabel x).

Definition WriteEvents(G: Graph): set Event :=
  fun e => exists x v, G.(Lab) e = Some (WriteLabel x v).

Definition FenceEvents(G: Graph): set Event :=
  fun e => G.(Lab) e = Some FenceLabel.

Definition ErrorEvents(G: Graph): set Event :=
  fun e => G.(Lab) e = Some ErrorLabel.

Definition Typ(G: Graph)(e: Event): EventTyp :=
  match G.(Lab) e with
  | Some l => LabelTyp l
  | None => ErrorEvent
  end.

Definition Loc(G: Graph)(e: Event): option word :=
  match G.(Lab) e with
  | Some l => match l with
              | ReadLabel x => Some x
              | WriteLabel x v => Some x
              | FenceLabel => None
              | ErrorLabel => None
              end
  | None => None
  end.

Definition Val(G: Graph)(e: Event): option w8 :=
  match G.(Lab) e with
  | Some l => match l with
              | ReadLabel x => None
              | WriteLabel x v => Some v
              | FenceLabel => None
              | ErrorLabel => None
              end
  | None => None
  end.

(* reads-from relation: `RfRel g e1 e2` means "e2 reads from e1" *)
Inductive RfRel(G: Graph): Event -> Event -> Prop :=
  mkRfRel: forall r, r \in ReadEvents G -> RfRel G (G.(Rf) r) r.

(* address dependency relation: `AddrRel g e1 e2` means "e2 has an address dependency on e1" *)
Definition AddrRel(G: Graph)(r e: Event): Prop := r \in G.(Addr) e.
Definition DataRel(G: Graph)(r e: Event): Prop := r \in G.(Data) e.
Definition CtrlRel(G: Graph)(r e: Event): Prop := r \in G.(Ctrl) e.

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
  fun e' => e \in ThreadEvents G /\
            trcl (unionrel (RfRel G) (unionrel (AddrRel G) (unionrel (DataRel G) (CtrlRel G)))) e' e.

(* Well-prefixed models include all the porf-acyclic ones,
   as well as ARMv7, ARMv8, IMM, LKMM, POWER, and RISC-V. *)
Definition wellPrefixed(G: Graph): Prop := forall e, ~ e \in prefix G e.

Instance Registers: map.map Z word := _.

Record ThreadState := mkThreadState {
  Regs: Registers;
  Pc: word;
  NextPc: word;
  Prog: list w32;
  CurrentEvent: Event;
  Deps: Register -> set Event;
}.

Instance ThreadStateSettable : Settable ThreadState :=
  settable! mkThreadState <Regs; Pc; NextPc; Prog; CurrentEvent; Deps>.

(* Tracking dependencies:

   Solution A (not chosen)
   Tracking data dependencies:
   - new MachineWidth instance where t is (t * Dependencies),
   - ternary if that tracks dependencies, and regular ifs that want
     to drop dependencies need to do regToBool
   - shift amount uses t
   - load and store return/take t instead of word8/16/32/64
   - allows us to remove some regToInt etc functions from MachineWidth
   Tracking control dependencies:
   - add an addCtrlDependency method to the RiscvProgram typeclass?

   Solution B (chosen)
   The dependency tracking is static, so we don't need to run execute to know what it does.
   Separate dependency update function that we run in endCycleNormal.
*)

(* If we have a primitive program `p` of type `M A`, then `p G s1 s2 a` means that
   under the global given graph G, starting in thread state s1 can end in state s2
   and produce answer a.
   In monadspeak: M is the combination of the reader monad (for the graph), the
   state monad (for ThreadState and A) and some "assertion monad" (the ... -> Prop). *)
Definition M(A: Type) := Graph -> ThreadState -> ThreadState -> A -> Prop.

Instance M_Monad: Monad M. refine ({|
  Bind A B (m: M A) (f: A -> M B) :=
    fun (G: Graph) (s1 s3: ThreadState) (b: B) =>
      exists a s2, m G s1 s2 a /\ f a G s2 s3 b;
  Return A (a : A) :=
    fun (G: Graph) (s1 s2: ThreadState) (a': A) =>
      s1 = s2 /\ a' = a;
|}).
all: prove_monad_law.
Defined.

(* state monad: *)
Definition get: M ThreadState := fun G s1 s2 a => s1 = s2 /\ a = s2.
Definition put(s: ThreadState): M unit := fun G s1 s2 a => s2 = s.

(* reader monad: *)
Definition ask: M Graph := fun G s1 s2 a => s1 = s2 /\ G = a.

(* assertion monad: *)
Definition assert(P: Prop): M unit := fun G s1 s2 a => s1 = s2 /\ P.
Definition fail_hard{A: Type}: M A := fun G s1 s2 a => False.

Definition getReg(regs: Registers)(reg: Z): word :=
  if Z.eq_dec reg 0 then word.of_Z 0
  else match map.get regs reg with
       | Some x => x
       | None => word.of_Z 0
       end.

Definition setReg(regs: Registers)(reg: Z)(v: word): Registers :=
  if Z.eq_dec reg Register0 then regs else map.put regs reg v.

Definition extractOption{A: Type}(o: option A): M A :=
  match o with
  | Some a => Return a
  | None => fail_hard
  end.

Definition loadInstruction(n: nat)(a: word): M (HList.tuple byte n) :=
  match n with
  | 4 => s <- get; extractOption (nth_error s.(Prog) (Z.to_nat ((word.unsigned a) / 4)))
  | _ => fail_hard
  end.

(* load_byte and store_byte do everything that GEN from the paper does except the
   {addr,data,ctrl} assertions in the for loop, because for these, we need to know
   the register names, so we move these assertions into preExec *)
Definition load_byte(addr: word): M w8 :=
  s <- get;
  G <- ask;
  assert (G.(Lab) s.(CurrentEvent) = Some (ReadLabel addr));;
  v <- extractOption (Val G (Rf G s.(CurrentEvent)));
  put (s <| CurrentEvent ::= NextEvent |>);;
  Return v.

Definition store_byte(addr: word)(v: w8): M unit :=
  s <- get;
  G <- ask;
  assert (G.(Lab) s.(CurrentEvent) = Some (WriteLabel addr v));;
  put (s <| CurrentEvent ::= NextEvent |>).

(* only 1-byte loads and stores are supported at the moment *)
Definition loadData(n: nat)(a: word): M (HList.tuple byte n) :=
  match n with
  | 1 => load_byte a
  | _ => fail_hard
  end.

Definition storeData(n: nat)(a: word): HList.tuple byte n -> M unit :=
  match n with
  | 1 => store_byte a
  | _ => fun _ => fail_hard
  end.

Definition loadN(n: nat)(kind: SourceType)(a: word): M (HList.tuple byte n) :=
  match kind with
  | Fetch => loadInstruction n a
  | Execute => loadData n a
  | VirtualMemory => fail_hard
  end.

Definition storeN(n: nat)(kind: SourceType)(a: word)(v: HList.tuple byte n): M unit :=
  s <- get;
  match kind with
  | Fetch => fail_hard
  | Execute => storeData n a v
  | VirtualMemory => fail_hard
  end.

Definition TODO{T: Type}: T. Admitted.

Definition pc: Register := -1%Z.

Definition getDeps(D: Register -> set Event)(r: Register): set Event :=
  if Z.eqb r 0 then empty_set else D r.

Definition setDeps(D: Register -> set Event)(r: Register)(s: set Event): Register -> set Event :=
  if Z.eqb r 0 then D else fun r0 => if Z.eqb r0 r then s else D r0.

Notation "D <[ r ]>" := (getDeps D r) (at level 8, left associativity, format "D <[ r ]>").
Notation "D <[ r := s ]>" := (setDeps D r s) (at level 8, left associativity, format "D <[ r  :=  s ]>").

Definition checkDepsI(inst: InstructionI): M unit :=
  match inst with
  (* only loading/storing one byte at a time is supported, the others will fail in load/storeData *)
  | Lb rd rs1 oimm12 => s <- get; G <- ask; assert (
       G.(Addr) s.(CurrentEvent) = s.(Deps)<[rs1]> /\
       G.(Data) s.(CurrentEvent) = empty_set /\
       G.(Ctrl) s.(CurrentEvent) = s.(Deps)<[pc]>
    )
  | Sb rs1 rs2 simm12 => s <- get; G <- ask; assert (
       G.(Addr) s.(CurrentEvent) = s.(Deps)<[rs1]> /\
       G.(Data) s.(CurrentEvent) = s.(Deps)<[rs2]> /\
       G.(Ctrl) s.(CurrentEvent) = s.(Deps)<[pc]>
    )
  (* instructions other than load/store need no dependency checking *)
  | _ => Return tt
  end.

Definition checkDeps(inst: Instruction): M unit :=
  match inst with
  | IInstruction i => checkDepsI i
  | _ => fail_hard (* only I is supported at the moment *)
  end.

Definition updateDepsI(inst: InstructionI)(D: Register -> set Event): Register -> set Event :=
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

Definition updateDeps(inst: Instruction): (Register -> set Event) -> (Register -> set Event) :=
  match inst with
  | IInstruction i => updateDepsI i
  | _ => id (* only I is supported at the moment *)
  end.

Instance IsRiscvMachine: RiscvProgram M word :=  {
  getRegister reg := s <- get; Return (getReg s.(Regs) reg);
  setRegister reg v := s <- get; put (s<|Regs := setReg s.(Regs) reg v|>);
  getPC := s <- get; Return s.(Pc);
  setPC newPc := s <- get; put (s<|NextPc := newPc|>);

  loadByte   := loadN 1;
  loadHalf   := loadN 2;
  loadWord   := loadN 4;
  loadDouble := loadN 8;

  storeByte   := storeN 1;
  storeHalf   := storeN 2;
  storeWord   := storeN 4;
  storeDouble := storeN 8;

  (* atomics, CSRs, and non-machine modes are not supported *)
  makeReservation  addr := fail_hard;
  clearReservation addr := fail_hard;
  checkReservation addr := fail_hard;
  getCSRField f := fail_hard;
  setCSRField f v := fail_hard;
  getPrivMode := fail_hard;
  setPrivMode v := fail_hard;

  endCycleNormal := s <- get; put (s<|Pc := s.(NextPc)|><|NextPc := word.add s.(NextPc) (word.of_Z 4)|>);

  (* exceptions are not supported *)
  endCycleEarly{A: Type} := fail_hard;
}.

Definition post_execute(inst: Instruction): M unit :=
  s <- get; put (s<|Deps := updateDeps inst s.(Deps)|>).

Definition pre_execute(inst: Instruction): M unit := checkDeps inst.

Definition run1: M unit :=
  pc <- getPC;
  w <- loadWord Fetch pc;
  let inst := decode RV32I (LittleEndian.combine 4 w) in
  pre_execute inst;;
  execute inst;;
  post_execute inst;;
  endCycleNormal.

(* the end of an execution is reached when the pc points one past the last instruction
   in the list of instructions *)
Inductive runToEnd(G: Graph): ThreadState -> ThreadState -> Prop :=
| RDone: forall s,
    Z.to_nat (word.unsigned s.(Pc) / 4) = length s.(Prog) ->
    runToEnd G s s
| RStep: forall s1 s2 s3,
    run1 G s1 s2 tt ->
    runToEnd G s2 s3 ->
    runToEnd G s1 s3.

Definition initialRegs: Registers := map.of_list_Z_at 1 (List.repeat (word.of_Z 0) 31).

Definition initialState(id: Tid)(prog: list Instruction): ThreadState := {|
  Regs := initialRegs;
  Pc := word.of_Z 0;
  NextPc := word.of_Z 4;
  Prog := List.map (fun inst => LittleEndian.split 4 (encode inst)) prog;
  CurrentEvent := ThreadEvent id 0;
  Deps := fun reg => empty_set;
|}.

Ltac inv H := inversion H; clear H; subst.

Require Import riscv.Utility.InstructionCoercions. Open Scope ilist_scope.
Require Import riscv.Utility.RegisterNames.
Require Import riscv.Spec.PseudoInstructions.

(* s1 := s0 by making a detour throug memory *)
Definition readAfterWriteProg := [[
  Sb a0 s0 0;
  Lb s1 a0 0
]].

Ltac simpl_exec :=
  cbn -[w8 w32 map.empty word.of_Z word.unsigned word.and word.add getReg map.put initialRegs] in *.

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

Lemma readAfterWriteWorks: forall G final,
    Wf G ->
    consSC G ->
    runToEnd G (initialState 0%nat readAfterWriteProg) final ->
    word.and (getReg final.(Regs) s1) (word.of_Z 255) =
    word.and (getReg final.(Regs) s0) (word.of_Z 255).
Proof.
  unfold initialState, s0, s1. intros *. intro W. intros.

  (* Sb a0 s0 0 *)
  inv H0. 1: discriminate H1.
  unfold run1 in H1.
  simpl_exec.
  simp.
  unfold extractOption, pre_execute, get, put in *.
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
  unfold extractOption, pre_execute, get, put, assert, ask in *.
  simp.
  simpl_exec.

  (* Lb s1 a0 0 *)
  inv H2. 1: discriminate H0.
  unfold run1 in H0.
  simpl_exec.
  simp.
  unfold extractOption, pre_execute, get, put in *.
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
  unfold extractOption, pre_execute, get, put, assert, ask in *.
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
    unfold extractOption, pre_execute, get, put in *.
    simp.
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
Time Qed. (* 13s *)

(* register a0 contains the address of the one-element FIFO,
   register a1 contains the address of the isEmpty flag,
   register s0 contains the value to be put into the FIFO *)
Definition writerProg := [[
  Sb a0 s0 0;   (* store the value into the FIFO *)
  Sb a1 zero 0  (* set the isEmpty flag to false *)
]].

Definition readerProg := [[
  Lb t0 a1 0;   (* start: t0 := isEmpty *)
  Beqz t0 (-4); (* if (isEmpty) { goto start } *)
  Lb s0 a0 0    (* read value from FIFO *)
]].

(* TODO more setup/preconditions on initial state will be needed (a0, a1) *)
Definition initialReaderState := initialState 0%nat writerProg.
Definition initialWriterState := initialState 1%nat readerProg.

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
  unfold extractOption in *. simp.
  simpl_exec.
  simp.
  unfold pre_execute, checkDeps in *.
  simp.
  unfold get in *.
  simp.
  simpl_exec.
  cbv in E.
  simp.
  cbv in E0.
  simp.
  simpl_exec.
  simp.
  unfold get in *.
  simp.
  unfold assert, ask in *.
  simpl_exec.
  simp.
  unfold extractOption in *.
  simp.
  simpl_exec.
  simp.
  unfold put in *.
  subst.
  simpl_exec.
  cbv delta [RecordSet.set] in H0.
  simpl_exec.

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
