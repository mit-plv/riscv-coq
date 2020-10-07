Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List. Import ListNotations.
Require Import coqutil.Tactics.Tactics.
Require Import riscv.Spec.Decode.
Require Import riscv.Spec.Machine.
Require Import riscv.Utility.Monads.
Require Import riscv.Utility.MonadNotations.
Require Import riscv.Utility.Utility.
Require Import riscv.Platform.Run.
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

(* Weak memory formalization following
   Kokologiannakis and Vafeiadis: HMC Model Checking for Hardware Memory Models, ASPLOS 2020 *)

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
| WriteLabel(o: AccessMode)(s: Exclusiveness)(x: word)(v: byte)
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

Definition Events(g: Graph): set Event :=
  fun e => exists l, g.(Lab) e = Some l.

Definition InitializationEvents(g: Graph): set Event :=
  fun e => exists x o v, e = InitEvent x /\ g.(Lab) e = Some (WriteLabel o NotExclusive x v).

Definition ThreadEvents(g: Graph): set Event :=
  fun e => exists l t i, e = ThreadEvent t i /\ g.(Lab) e = Some l.

Definition ReadEvents(g: Graph): set Event :=
  fun e => exists o s x, g.(Lab) e = Some (ReadLabel o s x).

Definition WriteEvents(g: Graph): set Event :=
  fun e => exists o s x v, g.(Lab) e = Some (WriteLabel o s x v).

Definition FenceEvents(g: Graph): set Event :=
  fun e => exists o, g.(Lab) e = Some (FenceLabel o).

Definition ErrorEvents(g: Graph): set Event :=
  fun e => g.(Lab) e = Some ErrorLabel.

Definition Typ(g: Graph)(e: Event): EventTyp :=
  match g.(Lab) e with
  | Some l => LabelTyp l
  | None => ErrorEvent
  end.

(* reads-from relation: `RfRel g e1 e2` means "e2 reads from e1" *)
Inductive RfRel(g: Graph): Event -> Event -> Prop :=
  mkRfRel: forall r, r \in ReadEvents g -> RfRel g (g.(Rf) r) r.

(* address dependency relation: `AddrRel g e1 e2` means "e2 has an address dependency on e1" *)
Definition AddrRel(g: Graph)(r e: Event): Prop := r \in Addr g e.
Definition DataRel(g: Graph)(r e: Event): Prop := r \in Data g e.
Definition CtrlRel(g: Graph)(r e: Event): Prop := r \in Ctrl g e.

Definition DependencyEdgesInProgramOrder(g: Graph): Prop :=
  subrel (AddrRel g) po /\ subrel (DataRel g) po /\ subrel (CtrlRel g) po.



Instance Registers: map.map Z word := _.

Record ThreadState := mkThreadState {
  Regs: Registers;
  Pc: word;
  NextPc: word;
  Prog: list w32;
  EventCount: nat;
  Deps: Register -> set Event;
}.

Instance ThreadStateSettable : Settable ThreadState :=
  settable! mkThreadState <Regs; Pc; NextPc; Prog; EventCount; Deps>.

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
  | 4 => s <- get; extractOption (nth_error s.(Prog) (Z.to_nat (word.unsigned a)))
  | _ => fail_hard
  end.

Definition loadData(n: nat)(a: word): M (HList.tuple byte n) :=
  match n with
  | 1 => s <- get; put (s <| EventCount ::= S |>);; fail_hard
  | _ => fail_hard
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
  | Execute => fail_hard
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

Definition currentInstruction: M Instruction :=
  s <- get;
  w <- extractOption (nth_error s.(Prog) (Z.to_nat (word.unsigned s.(Pc))));
  Return (decode RV32I (LittleEndian.combine 4 w)).

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

  makeReservation  addr := fail_hard;
  clearReservation addr := fail_hard;
  checkReservation addr := fail_hard;
  getCSRField f := fail_hard;
  setCSRField f v := fail_hard;
  getPrivMode := fail_hard;
  setPrivMode v := fail_hard;

  endCycleNormal :=
    s <- get;
    inst <- currentInstruction;
    put (s<|Pc := s.(NextPc)|>
          <|NextPc := word.add s.(NextPc) (word.of_Z 4)|>
          <|Deps := updateDeps inst s.(Deps)|>);
  endCycleEarly{A: Type} := fail_hard;
}.

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
