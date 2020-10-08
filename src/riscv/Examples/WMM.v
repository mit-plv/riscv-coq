Require Import Coq.ZArith.ZArith.
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

(* sub-relation *)
Definition subrel{A B: Type}(R1 R2: A -> B -> Prop): Prop :=
  forall a b, R1 a b -> R2 a b.

Definition unionrel{A B: Type}(R1 R2: A -> B -> Prop): A -> B -> Prop :=
  fun a b => R1 a b \/ R2 a b.

Definition invrel{A B: Type}(R: A -> B -> Prop): B -> A -> Prop := fun b a => R a b.

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

Inductive Exclusiveness := NotExclusive | Exclusive.

Inductive AccessMode := oR | oW. (* QUESTION: seems to duplicate Read/Write info of Label? *)

Inductive Label :=
| ReadLabel(o: AccessMode)(s: Exclusiveness)(x: word)
| WriteLabel(o: AccessMode)(s: Exclusiveness)(x: word)(v: w8)
| FenceLabel(o: AccessMode)
| ErrorLabel.

Inductive EventTyp := ReadEvent | WriteEvent | FenceEvent | ErrorEvent.

Definition LabelTyp(l: Label): EventTyp :=
  match l with
  | ReadLabel _ _ _ => ReadEvent
  | WriteLabel _ _ _ _ => WriteEvent
  | FenceLabel _ => FenceEvent
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
  fun e => exists x o v, e = InitEvent x /\ G.(Lab) e = Some (WriteLabel o NotExclusive x v).

Definition ThreadEvents(G: Graph): set Event :=
  fun e => exists l t i, e = ThreadEvent t i /\ G.(Lab) e = Some l.

Definition ReadEvents(G: Graph): set Event :=
  fun e => exists o s x, G.(Lab) e = Some (ReadLabel o s x).

Definition ExclusiveReadEvents(G: Graph): set Event :=
  fun e => exists o x, G.(Lab) e = Some (ReadLabel o Exclusive x).

Definition NotExclusiveReadEvents(G: Graph): set Event :=
  fun e => exists o x, G.(Lab) e = Some (ReadLabel o NotExclusive x).

Definition WriteEvents(G: Graph): set Event :=
  fun e => exists o s x v, G.(Lab) e = Some (WriteLabel o s x v).

Definition ExclusiveWriteEvents(G: Graph): set Event :=
  fun e => exists o x v, G.(Lab) e = Some (WriteLabel o Exclusive x v).

Definition NotExclusiveWriteEvents(G: Graph): set Event :=
  fun e => exists o x v, G.(Lab) e = Some (WriteLabel o NotExclusive x v).

Definition FenceEvents(G: Graph): set Event :=
  fun e => exists o, G.(Lab) e = Some (FenceLabel o).

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
              | ReadLabel o s x => Some x
              | WriteLabel o s x v => Some x
              | FenceLabel o => None
              | ErrorLabel => None
              end
  | None => None
  end.

Definition Val(G: Graph)(e: Event): option w8 :=
  match G.(Lab) e with
  | Some l => match l with
              | ReadLabel o s x => None
              | WriteLabel o s x v => Some v
              | FenceLabel o => None
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

Definition RMW_Atomicity(G: Graph): Prop :=
  forall r1 r2,
    r1 \in ExclusiveReadEvents G ->
    r2 \in ExclusiveReadEvents G ->
    r1 <> r2 ->
    NextEvent r1 \in ExclusiveWriteEvents G ->
    NextEvent r2 \in ExclusiveWriteEvents G ->
    G.(Rf) r1 = G.(Rf) r2 ->
    False.

(* sequential consistency *)
Definition consSC(G: Graph): Prop :=
  RMW_Atomicity G /\
  exists mo, modificationOrder G mo /\ acyclic (unionrel po (unionrel (RfRel G) (invrel (RfRel G)))).

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
  assert (G.(Lab) s.(CurrentEvent) = Some (ReadLabel oR NotExclusive addr));;
  v <- extractOption (Val G (Rf G s.(CurrentEvent)));
  put (s <| CurrentEvent ::= NextEvent |>);;
  Return v.

Definition store_byte(addr: word)(v: w8): M unit :=
  s <- get;
  G <- ask;
  assert (G.(Lab) s.(CurrentEvent) = Some (WriteLabel oW NotExclusive addr v)).

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

Definition initialState(id: Tid)(prog: list Instruction): ThreadState := {|
  Regs := map.empty;
  Pc := word.of_Z 0;
  NextPc := word.of_Z 4;
  Prog := List.map (fun inst => LittleEndian.split 4 (encode inst)) prog;
  CurrentEvent := ThreadEvent id 0;
  Deps := fun reg => empty_set;
|}.

Require Import riscv.Utility.InstructionCoercions. Open Scope ilist_scope.
Require Import riscv.Utility.RegisterNames.
Require Import riscv.Spec.PseudoInstructions.

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

Ltac inv H := inversion H; clear H; subst.

Lemma message_passing_works: forall G finalReaderState finalWriterState,
    consSC G ->
    runToEnd G initialReaderState finalReaderState ->
    runToEnd G initialWriterState finalWriterState ->
    getReg finalWriterState.(Regs) s0 = getReg initialWriterState.(Regs) s0.
Proof.
  intros *. intros Co RR RW.
  inv RW. 1: discriminate H.
  unfold run1, initialWriterState, initialState in H.
  cbn -[w32 map.empty word.of_Z word.unsigned] in H.
  simp.
  unfold extractOption in *. simp.
  cbn -[w32 map.empty word.of_Z word.unsigned getReg setReg] in *.
  simp.
  unfold pre_execute, checkDeps in *.
  simp.
  unfold get in *.
  simp.
  cbn -[w32 map.empty word.of_Z word.unsigned getReg setReg] in *.
  cbv in E.
  simp.
  cbv in E0.
  simp.
  cbn -[w32 map.empty word.of_Z word.unsigned getReg setReg] in *.
  simp.
  unfold get in *.
  simp.
  unfold assert, ask in *.
  cbn -[w32 map.empty word.of_Z word.unsigned getReg setReg] in *.
  simp.
  unfold extractOption in *.
  simp.
  cbn -[w32 map.empty word.of_Z word.unsigned getReg setReg] in *.
  simp.
  unfold put in *.
  subst.
  cbn -[w32 map.empty word.of_Z word.unsigned getReg setReg] in *.
  cbv delta [RecordSet.set] in H0;
  cbn -[w32 map.empty word.of_Z word.unsigned getReg setReg] in *.

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
