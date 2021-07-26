Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.
Require Import riscv.Utility.Monads.
Require Import riscv.Utility.MonadNotations.
Require Import riscv.Spec.Decode.
Require Import riscv.Spec.Machine.
Require Import riscv.Utility.Utility.
Require Import riscv.Spec.Primitives.
Require Import Coq.Lists.List. Import ListNotations.
Require Import coqutil.Datatypes.List.
Require Import coqutil.Datatypes.ListSet.
Require Export riscv.Platform.RiscvMachine.
Require Import coqutil.Z.Lia.
Require Import coqutil.Map.Interface.
Require Import coqutil.Map.Properties.
Require Import coqutil.Datatypes.PropSet.
Require Import coqutil.Tactics.Tactics.
Require Import riscv.Platform.Sane.

Local Open Scope Z_scope.
Local Open Scope bool_scope.


Class MMIOSpec{width: Z}{BW: Bitwidth width}{word: word width} := {
  (* should not say anything about alignment, just whether it's in the MMIO range *)
  isMMIOAddr: word -> Prop;

  (* alignment and load size checks *)
  isMMIOAligned: nat -> word -> Prop;
}.

Section Riscv.
  Context {width: Z} {BW: Bitwidth width} {word: word width} {word_ok: word.ok word}.
  Context {Mem: map.map word byte} {Registers: map.map Register word}.

  Definition signedByteTupleToReg{n: nat}(v: HList.tuple byte n): word :=
    word.of_Z (BitOps.signExtend (8 * Z.of_nat n) (LittleEndian.combine n v)).

  Definition mmioLoadEvent(addr: word){n: nat}(v: HList.tuple byte n): LogItem :=
    ((map.empty, "MMIOREAD"%string, [addr]), (map.empty, [signedByteTupleToReg v])).

  Definition mmioStoreEvent(addr: word){n: nat}(v: HList.tuple byte n): LogItem :=
    ((map.empty, "MMIOWRITE"%string, [addr; signedByteTupleToReg v]), (map.empty, [])).

  Context {mmio_spec: MMIOSpec}.

  Definition nonmem_store(n: nat)(ctxid: SourceType) a v mach post :=
    isMMIOAddr a /\ isMMIOAligned n a /\
    post (withXAddrs (invalidateWrittenXAddrs n a mach.(getXAddrs))
         (withLogItem (@mmioStoreEvent a n v)
         mach)).

  Definition store(n: nat)(ctxid: SourceType) a v mach post :=
    match Memory.store_bytes n mach.(getMem) a v with
    | Some m => post (withXAddrs (invalidateWrittenXAddrs n a mach.(getXAddrs)) (withMem m mach))
    | None => nonmem_store n ctxid a v mach post
    end.

  Definition nonmem_load(n: nat)(ctxid: SourceType) a mach (post: _ -> _ -> Prop) :=
    isMMIOAddr a /\ isMMIOAligned n a /\
    forall v, post v (withLogItem (@mmioLoadEvent a n v) mach).

  Definition load(n: nat)(ctxid: SourceType) a mach post :=
    (ctxid = Fetch -> isXAddr4 a mach.(getXAddrs)) /\
    match Memory.load_bytes n mach.(getMem) a with
    | Some v => post v mach
    | None => nonmem_load n ctxid a mach post
    end.

  Instance IsRiscvMachine: RiscvProgram (Post RiscvMachine) word. refine ({|
    getRegister reg := fun mach post => _;
    setRegister reg v := fun mach post => _;
    loadByte   ctxid a := fun mach post => _;
    loadHalf   ctxid a := fun mach post => _;
    loadWord   ctxid a := fun mach post => _;
    loadDouble ctxid a := fun mach post => _;
    storeByte   ctxid a v := fun mach post => _;
    storeHalf   ctxid a v := fun mach post => _;
    storeWord   ctxid a v := fun mach post => _;
    storeDouble ctxid a v := fun mach post => _;
    makeReservation _  := fun _ _ => False;
    clearReservation _ := fun _ _ => False;
    checkReservation _ := fun _ _ => False;
    getPC := fun mach post => _;
    setPC newPC := fun mach post => _;
    getCSRField _      := fun _ _ => False;
    setCSRField _ _    := fun _ _ => False;
    getPrivMode        := fun _ _ => False;
    setPrivMode _      := fun _ _ => False;
    fence _ _          := fun _ _ => False;
    endCycleEarly _    := fun _ _ => False;
    endCycleNormal     := fun mach post => _;
  |}).
  (* TODO: inline the terms below into the holes above while keeping Coq's typechecker happy *)
  - exact (let v :=
        if Z.eq_dec reg 0 then word.of_Z 0
        else match map.get mach.(getRegs) reg with
             | Some x => x
             | None => word.of_Z 0 end in
           post v mach).
  - exact (let regs := if Z.eq_dec reg Register0
                       then mach.(getRegs)
                       else map.put mach.(getRegs) reg v in
      post tt (withRegs regs mach)).
  - exact (load 1 ctxid a mach post).
  - exact (load 2 ctxid a mach post).
  - exact (load 4 ctxid a mach post).
  - exact (load 8 ctxid a mach post).
  - exact (store 1 ctxid a v mach (post tt)).
  - exact (store 2 ctxid a v mach (post tt)).
  - exact (store 4 ctxid a v mach (post tt)).
  - exact (store 8 ctxid a v mach (post tt)).
  - exact (post mach.(getPc) mach).
  - exact (post tt (withNextPc newPC mach)).
  - exact (post tt (withPc mach.(getNextPc) (withNextPc (word.add mach.(getNextPc) (word.of_Z 4)) mach))).
  Defined.

  Definition MinimalMMIOPrimitivesParams: PrimitivesParams (Post RiscvMachine) RiscvMachine := {|
    Primitives.mcomp_sat A (m: Post RiscvMachine A) mach post := m mach post;
    Primitives.is_initial_register_value x := True;
    Primitives.nonmem_load := nonmem_load;
    Primitives.nonmem_store := nonmem_store;
    Primitives.valid_machine mach :=
      map.undef_on mach.(getMem) isMMIOAddr /\ disjoint (of_list mach.(getXAddrs)) isMMIOAddr;
  |}.

  Lemma load_weaken_post n c a m (post1 post2:_->_->Prop)
    (H: forall r s, post1 r s -> post2 r s)
    : load n c a m post1 -> load n c a m post2.
  Proof.
    cbv [load nonmem_load].
    destruct (Memory.load_bytes n (getMem m) a); intuition eauto.
  Qed.

  Lemma store_weaken_post n c a v m (post1 post2:_->Prop)
    (H: forall s, post1 s -> post2 s)
    : store n c a v m post1 -> store n c a v m post2.
  Proof.
    cbv [store nonmem_store].
    destruct (Memory.store_bytes n (getMem m) a); intuition eauto.
  Qed.

  (* all the monadic riscv computations we will construct satisfy weakening, but it is not
     explicit from the type *)
  Definition weakening_for{S A: Type}(m: Post S A): Prop :=
    forall post1 post2: A -> S -> Prop,
      (forall a s, post1 a s -> post2 a s) ->
      forall s, m s post1 -> m s post2.

  Global Instance MinimalMMIOSatisfies_mcomp_sat_spec: mcomp_sat_spec MinimalMMIOPrimitivesParams.
  Proof.
    split; cbv [mcomp_sat MinimalMMIOPrimitivesParams Bind Return Post_Monad
                PostMonadOperations.weaken]; intros. 2: reflexivity.
    (* spec_Bind *)
    split; intros.
    - destruct H as (mid & ? & ?).
      (* can't get weakening because the type "Post RiscvMachine A" does not guarantee that all
         its inhabitant were constructed using the RiscvProgram primitives *)
  Abort.

  Lemma preserve_undef_on{memOk: map.ok Mem}: forall n (m m': Mem) a w s,
      Memory.store_bytes n m a w = Some m' ->
      map.undef_on m s ->
      map.undef_on m' s.
  Proof.
    eauto using map.same_domain_preserves_undef_on, Memory.store_bytes_preserves_domain.
  Qed.

  Global Instance MinimalMMIOPrimitivesSane{memOk: map.ok Mem} :
    PrimitivesSane MinimalMMIOPrimitivesParams.
  Abort.

  Global Instance MinimalMMIOSatisfiesPrimitives{memOk: map.ok Mem} :
    Primitives MinimalMMIOPrimitivesParams.
  Abort.

End Riscv.
