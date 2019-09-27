Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Logic.PropExtensionality.
Require Import riscv.Utility.Monads.
Require Import riscv.Utility.MonadNotations.
Require Import riscv.Spec.Decode.
Require Import riscv.Spec.Machine.
Require Import riscv.Utility.Utility.
Require Import riscv.Spec.Primitives.
Require Import Coq.Lists.List. Import ListNotations.
Require Export riscv.Utility.MMIOTrace.
Require Export riscv.Platform.RiscvMachine.
Require Import coqutil.Z.Lia.
Require Import coqutil.Map.Interface.
Require Import coqutil.Tactics.Tactics.
Require Import riscv.Platform.Sane.

Local Open Scope Z_scope.
Local Open Scope bool_scope.

(* TODO: move *)
Module Import List.
  Definition endswith {T} (xs : list T) (suffix : list T) :=
    exists prefix, xs = prefix ++ suffix.
  Lemma endswith_refl {T} (xs : list T) : endswith xs xs.
  Proof. exists nil; trivial. Qed.
  Lemma endswith_cons_l {T} (x : T) xs ys :
    endswith ys xs -> endswith (cons x ys) xs.
  Proof. inversion 1; subst. eexists (cons x _). exact eq_refl. Qed.
End List.

(* TODO: move *)
Module free.
  Section WithInterface.
    Context {action : Type} {result : action -> Type}.
    Inductive free {T : Type} : Type :=
    | act (a : action) (_ : result a -> free)
    | ret (x : T).
    Arguments free : clear implicits.

    Fixpoint bind {A B} (mx : free A) (fy : A -> free B) : free B :=
      match mx with
      | act a k => act a (fun x => bind (k x) fy)
      | ret x => fy x
      end.

    (** Monad laws *)
    Definition bind_ret_l {A B} a b : @bind A B (ret a) b = b a := eq_refl.
    Lemma bind_assoc {A B C} (a : free A) (b : A -> free B) (c : B -> free C) :
      bind (bind a b) c = bind a (fun x => bind (b x) c).
    Proof. revert c; revert C; revert b; revert B; induction a;
        cbn [bind]; eauto using f_equal, functional_extensionality. Qed.
    Lemma bind_ret_r {A} (a : free A) : bind a ret = a.
    Proof. induction a;
        cbn [bind]; eauto using f_equal, functional_extensionality. Qed.
    Global Instance Monad_free : Monad free.
    Proof. esplit; eauto using bind_ret_l, bind_assoc, bind_ret_r. Defined.

    Section WithState.
      Context {state}
      (interp_action : forall a : action, state -> (result a -> state -> Prop) -> Prop).
      Section WithOutput.
        Context {output} (post : output -> state -> Prop).
        Definition interp_body interp (a : free output) (s : state) : Prop :=
          match a with
          | ret x => post x s
          | act a k => interp_action a s (fun r => interp (k r))
          end.
        Fixpoint interp_fix a := interp_body interp_fix a.
      End WithOutput.

      Definition interp {output} a s post := @interp_fix output post a s.

      Lemma interp_ret {T} (x : T) m P : interp (ret x) m P = P x m. 
      Proof. exact eq_refl. Qed.
      Lemma interp_act {T} a (k : _ -> free T) s post
        : interp (act a k) s post
        = interp_action a s (fun r s => interp (k r) s post).
      Proof. exact eq_refl. Qed.

      Context (interp_action_weaken_post :
        forall a (post1 post2:_->_->Prop), (forall r s, post1 r s -> post2 r s) -> forall s, interp_action a s post1 -> interp_action a s post2).

      Lemma interp_weaken_post {T} (p : free T) s
        (post1 post2:_->_->Prop) (Hpost : forall r s, post1 r s -> post2 r s)
        (Hinterp : interp p s post1) : interp p s post2.
      Proof. revert dependent s; induction p; cbn; firstorder eauto. Qed.

      Lemma interp_bind {A B} s post (a : free A) (b : A -> free B) :
        interp (bind a b) s post <-> interp a s (fun x s => interp (b x) s post).
      Proof.
        revert post; revert b; revert B; revert s; induction a.
        2: { intros. cbn. reflexivity. }
        split; eapply interp_action_weaken_post; intros; eapply H; eauto.
      Qed.

      Lemma interp_bind_ex_mid {A B} m0 post (a : free A) (b : A -> free B) :
        interp (bind a b) m0 post <-> 
        (exists mid, interp a m0 mid /\ forall x m1, mid x m1 -> interp (b x) m1 post).
      Proof.
        rewrite interp_bind.
        split; [intros ? | intros (?&?&?)].
        { exists (fun x m1 => interp (b x) m1 post); split; eauto. }
        { eauto using interp_weaken_post. }
      Qed.
    End WithState.

  End WithInterface.
  Global Arguments free : clear implicits.
End free. Notation free := free.free.

Class ExtSpec{W: Words}{mem : map.map word byte} := {
  mmio_load: forall (n: nat), SourceType -> word -> mem -> list LogItem -> (mem -> HList.tuple byte n -> Prop) -> Prop;
  mmio_store: forall (n: nat), SourceType -> word -> HList.tuple byte n -> mem -> list LogItem -> (mem -> Prop) -> Prop;
}.

Section Riscv.
  Import free.
  Context {W: Words} {Mem: map.map word byte} {Registers: map.map Register word}.

  Local Notation wxlen := word.
  Variant action :=
  | getRegister (_ : Register)
  | setRegister (_ : Register) (_ : wxlen)
  | loadByte (_ : SourceType) (_ : wxlen)
  | loadHalf (_ : SourceType) (_ : wxlen)
  | loadWord (_ : SourceType) (_ : wxlen)
  | loadDouble (_ : SourceType) (_ : wxlen)
  | storeByte (_ : SourceType) (_ : wxlen) (_ : w8)
  | storeHalf (_ : SourceType) (_ : wxlen) (_ : w16)
  | storeWord (_ : SourceType) (_ : wxlen) (_ : w32)
  | storeDouble (_ : SourceType) (_ : wxlen) (_ : w64)
  | makeReservation (_ : wxlen)
  | clearReservation (_ : wxlen)
  | checkReservation (_ : wxlen)
  | raiseExceptionWithInfo (_ : Type) (isInterrupt exceptionCode info : wxlen)
  | getPC
  | setPC (_ : wxlen)
  | step
  .

  Definition result (action : action) : Type :=
    match action with
    | getRegister _ => wxlen
    | setRegister _ _ => unit
    | loadByte _ _ => w8
    | loadHalf _ _ => w16
    | loadWord _ _ => w32
    | loadDouble _ _ => w64
    | storeByte _ _ _ | storeHalf _ _ _ | storeWord _ _ _ | storeDouble _ _ _ | makeReservation _ | clearReservation _ => unit
    | checkReservation _ => bool
    | raiseExceptionWithInfo T _ _ _ => T
    | getPC => wxlen
    | setPC _ | step => unit
    end.

  Local Notation M := (free action result).

  Instance IsRiscvMachine: RiscvProgram M word := {|
    Machine.getRegister a := act (getRegister a) ret;
    Machine.setRegister a b := act (setRegister a b) ret;
    Machine.loadByte a b := act (loadByte a b) ret;
    Machine.loadHalf a b := act (loadHalf a b) ret;
    Machine.loadWord a b := act (loadWord a b) ret;
    Machine.loadDouble a b := act (loadDouble a b) ret;
    Machine.storeByte a b c := act (storeByte a b c) ret;
    Machine.storeHalf a b c := act (storeHalf a b c) ret;
    Machine.storeWord a b c := act (storeWord a b c) ret;
    Machine.storeDouble a b c := act (storeDouble a b c) ret;
    Machine.makeReservation a := act (makeReservation a) ret;
    Machine.clearReservation a := act (clearReservation a) ret;
    Machine.checkReservation a := act (checkReservation a) ret;
    Machine.getPC := act getPC ret;
    Machine.setPC a := act (setPC a) ret;
    Machine.step := act step ret;
    Machine.raiseExceptionWithInfo a b c d := act (raiseExceptionWithInfo a b c d) ret;
  |}.

  Definition signedByteTupleToReg{n: nat}(v: HList.tuple byte n): word :=
    word.of_Z (BitOps.signExtend (8 * Z.of_nat n) (LittleEndian.combine n v)).

  Definition mmioLoadEvent(addr: word){n: nat}(v: HList.tuple byte n): LogItem :=
    ((map.empty, MMInput, [addr]), (map.empty, [signedByteTupleToReg v])).

  Definition mmioStoreEvent(addr: word){n: nat}(v: HList.tuple byte n): LogItem :=
    ((map.empty, MMOutput, [addr; signedByteTupleToReg v]), (map.empty, [])).

  Context {ext_spec: ExtSpec}.

  Definition store n ctxid a v mach post :=
    let XAddrs := invalidateWrittenXAddrs n a mach.(getXAddrs) in
    match Memory.store_bytes n mach.(getMem) a v with
    | Some m => post (withXAddrs XAddrs (withMem m mach))
    | None => mmio_store n ctxid a v mach.(getMem) mach.(getLog) (fun m =>
      post (withXAddrs XAddrs (withMem m (withLogItem (mmioStoreEvent a v) mach))))
    end.

  Definition load n ctxid a mach post :=
    (ctxid = Fetch -> isXAddr a mach.(getXAddrs)) /\
    match Memory.load_bytes n mach.(getMem) a with
    | Some v => post v mach
    | None => mmio_load n ctxid a mach.(getMem) mach.(getLog) (fun m v =>
      post v (withMem m (withLogItem (@mmioLoadEvent a n v) mach)))
    end.

  Definition interp_action (a : action) (mach : RiscvMachine) : (result a -> RiscvMachine -> Prop) -> Prop :=
    match a with
    | getRegister reg => fun post =>
        let v :=
          if Z.eq_dec reg 0 then word.of_Z 0
          else match map.get mach.(getRegs) reg with
               | Some x => x
               | None => word.of_Z 0 end in
        post v mach
    | setRegister reg v => fun post =>
      let regs := if Z.eq_dec reg Register0
                  then mach.(getRegs)
                  else map.put mach.(getRegs) reg v in
      post tt (withRegs regs mach)
    | getPC => fun post => post mach.(getPc) mach
    | setPC newPC => fun post => post tt (withNextPc newPC mach)
    | step => fun post => post tt (withPc mach.(getNextPc) (withNextPc (word.add mach.(getNextPc) (word.of_Z 4)) mach))
    | loadByte ctxid a => fun post => load 1 ctxid a mach post
    | loadHalf ctxid a => fun post => load 2 ctxid a mach post
    | loadWord ctxid a => fun post => load 4 ctxid a mach post
    | loadDouble ctxid a => fun post => load 8 ctxid a mach post
    | storeByte ctxid a v => fun post => store 1 ctxid a v mach (post tt)
    | storeHalf ctxid a v => fun post => store 2 ctxid a v mach (post tt)
    | storeWord ctxid a v => fun post => store 4 ctxid a v mach (post tt)
    | storeDouble ctxid a v => fun post => store 8 ctxid a v mach (post tt)
    | makeReservation _
    | clearReservation _
    | checkReservation _
    | raiseExceptionWithInfo _ _ _ _
        => fun _ => False
    end.
  
  Notation interp p mach post := (free.interp interp_action p mach post).

  Definition MinimalMMIOPrimitivesParams: PrimitivesParams M RiscvMachine := {|
    Primitives.mcomp_sat := @free.interp _ _ _ interp_action;
    Primitives.is_initial_register_value x := True;
    Primitives.nonmem_load n ctxid a mach post :=
      mmio_load n ctxid a mach.(getMem) mach.(getLog) (fun m v =>
      post v (withMem m (withLogItem (@mmioLoadEvent a n v) mach)));
    Primitives.nonmem_store n ctxid a v mach post :=
      let XAddrs := invalidateWrittenXAddrs n a mach.(getXAddrs) in
      mmio_store n ctxid a v mach.(getMem) mach.(getLog) (fun m =>
      post (withXAddrs XAddrs (withMem m (withLogItem (mmioStoreEvent a v) mach))));
  |}.

  Context
    (mmio_load_weaken_post : forall n c a m t (post1 post2:_->_->Prop), (forall m r, post1 m r -> post2 m r) -> mmio_load n c a m t post1 -> mmio_load n c a m t post2)
    (mmio_store_weaken_post : forall n c a v m t (post1 post2:_->Prop), (forall m, post1 m -> post2 m) -> mmio_store n c a v m t post1 -> mmio_store n c a v m t post2)
    (mmio_load_total : forall n c a m t post, mmio_load n c a m t post -> exists v s, post v s)
    (mmio_store_total : forall n c a v m t post, mmio_store n c a v m t post -> exists s, post s).

  Lemma load_weaken_post n c a m (post1 post2:_->_->Prop)
    (H: forall r s, post1 r s -> post2 r s)
    : load n c a m post1 -> load n c a m post2.
  Proof.
    cbv [load].
    destruct (Memory.load_bytes n (getMem m) a); intuition eauto.
    eapply mmio_load_weaken_post; eauto; intros. eapply H; eauto.
  Qed.

  Lemma store_weaken_post n c a v m (post1 post2:_->Prop)
    (H: forall s, post1 s -> post2 s)
    : store n c a v m post1 -> store n c a v m post2.
  Proof.
    cbv [store].
    destruct (Memory.store_bytes n (getMem m) a); intuition eauto.
    eapply mmio_store_weaken_post; eauto; intros. eapply H; eauto.
  Qed.

  Lemma interp_action_weaken_post a (post1 post2:_->_->Prop)
    (H: forall r s, post1 r s -> post2 r s) s
    : interp_action a s post1 -> interp_action a s post2.
  Proof.
    destruct a; cbn; try solve [intuition eauto].
    all : eauto using load_weaken_post, store_weaken_post.
  Qed.

  Global Instance MinimalMMIOSatisfies_mcomp_sat_spec: mcomp_sat_spec MinimalMMIOPrimitivesParams.
  Proof.
    split; cbv [mcomp_sat MinimalMMIOPrimitivesParams Bind Return Monad_free].
    { symmetry. eapply interp_bind_ex_mid, interp_action_weaken_post. }
    { symmetry; intros. rewrite interp_ret; eapply iff_refl. }
  Qed.

  Lemma interp_action_total a s post :
    interp_action a s post -> exists v s, post v s.
  Proof.
    destruct a; cbn -[HList.tuple]; cbv [load store]; cbn -[HList.tuple];
      repeat destruct_one_match; intuition eauto;
        try (eapply mmio_load_total in H1; destruct_products; eauto);
        try (eapply mmio_store_total in H; destruct_products; eauto).
  Qed.

  Import coqutil.Tactics.Tactics.
  Lemma interp_action_appendonly a s post :
    interp_action a s post ->
    interp_action a s (fun _ s' => endswith s'.(getLog) s.(getLog)).
  Proof.
    destruct s, a; cbn; cbv [load store]; cbn;
      repeat destruct_one_match;
      intuition eauto using endswith_refl, endswith_cons_l.
  Qed.

  (* NOTE: maybe instead a generic lemma to push /\ into postondition? *)
  Lemma interp_action_appendonly' a s post :
    interp_action a s post ->
    interp_action a s (fun v s' => post v s' /\ endswith s'.(getLog) s.(getLog)).
  Proof.
    destruct s, a; cbn; cbv [load store]; cbn;
      repeat destruct_one_match; intros; destruct_products; try split;
        try (eapply mmio_load_weaken_post; eauto);
        try (eapply mmio_store_weaken_post; eauto);
        intuition eauto using endswith_refl, endswith_cons_l.
  Qed.

  Global Instance MinimalMMIOPrimitivesSane : PrimitivesSane MinimalMMIOPrimitivesParams.
  Proof.
    split; cbv [mcomp_sane]; intros; 
      exact (conj (interp_action_total _ st _ H)
                  (interp_action_appendonly' _ _ _ H)).
  Qed.

  Global Instance MinimalMMIOSatisfiesPrimitives: Primitives MinimalMMIOPrimitivesParams.
  Proof.
    split; try exact _.
    all : cbv [mcomp_sat spec_load spec_store MinimalMMIOPrimitivesParams invalidateWrittenXAddrs].
    all: intros;
      repeat match goal with
      | _ => progress subst
      | _ => Option.inversion_option
      | _ => progress cbn -[Memory.load_bytes Memory.store_bytes HList.tuple]
      | _ => progress cbv [Register0 valid_register is_initial_register_value load store Memory.loadByte Memory.loadHalf Memory.loadWord Memory.loadDouble Memory.storeByte Memory.storeHalf Memory.storeWord Memory.storeDouble] in *
      | H : exists _, _ |- _ => destruct H
      | H : _ /\ _ |- _ => destruct H
      | |- _ => solve [ intuition (eauto || Lia.lia) ]
      | H : _ \/ _ |- _ => destruct H
      | |- context[match ?x with _ => _ end] => destruct x eqn:?
      | |-_ /\ _ => split
      end.
      (* setRegister *)
      destruct initialL; eassumption.
  Qed.

End Riscv.
