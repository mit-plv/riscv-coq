Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.
Require Import riscv.Utility.Monads.
Require Import riscv.Utility.MonadNotations.
Require Export riscv.Utility.FreeMonad.
Require Import riscv.Spec.Decode.
Require Import riscv.Spec.Machine.
Require Import riscv.Utility.Utility.
Require Import riscv.Spec.Primitives.
Require Import Coq.Lists.List. Import ListNotations.
Require Import coqutil.Datatypes.List.
Require Import coqutil.Datatypes.ListSet.
Require Export riscv.Platform.RiscvMachine.
Require Export riscv.Platform.MaterializeRiscvProgram.
Require Import coqutil.Z.Lia.
Require Import coqutil.Map.Interface.
Require Import coqutil.Map.Properties.
Require Import coqutil.Datatypes.PropSet.
Require Import coqutil.Tactics.Tactics.
Require Import riscv.Platform.Sane.

Local Open Scope Z_scope.
Local Open Scope bool_scope.

Section Riscv.
  Import free.
  Context {width: Z} {BW: Bitwidth width} {word: word width} {word_ok: word.ok word}.
  Context {Mem: map.map word byte} {Registers: map.map Register word}.

  Definition signedByteTupleToReg{n: nat}(v: HList.tuple byte n): word :=
    word.of_Z (BitOps.signExtend (8 * Z.of_nat n) (LittleEndian.combine n v)).

  Definition store(n: nat)(ctxid: SourceType) a v mach post :=
    match Memory.store_bytes n mach.(getMem) a v with
    | Some m => post (withXAddrs (invalidateWrittenXAddrs n a mach.(getXAddrs)) (withMem m mach))
    | None => False
    end.

  Definition load(n: nat)(ctxid: SourceType) a mach post :=
    (ctxid = Fetch -> isXAddr4 a mach.(getXAddrs)) /\
    match Memory.load_bytes n mach.(getMem) a with
    | Some v => post v mach
    | None => False
    end.

  Definition updatePc(mach: RiscvMachine): RiscvMachine :=
    withPc mach.(getNextPc) (withNextPc (word.add mach.(getNextPc) (word.of_Z 4)) mach).

  Definition interpret_action (a : riscv_primitive) (mach : RiscvMachine) :
    (primitive_result a -> RiscvMachine -> Prop) -> (RiscvMachine -> Prop) -> Prop :=
    match a with
    | GetRegister reg => fun (postF: word -> RiscvMachine -> Prop) postA =>
        let v :=
          if Z.eq_dec reg 0 then word.of_Z 0
          else match map.get mach.(getRegs) reg with
               | Some x => x
               | None => word.of_Z 0 end in
        postF v mach
    | SetRegister reg v => fun postF postA =>
      let regs := if Z.eq_dec reg Register0
                  then mach.(getRegs)
                  else map.put mach.(getRegs) reg v in
      postF tt (withRegs regs mach)
    | GetPC => fun postF postA => postF mach.(getPc) mach
    | SetPC newPC => fun postF postA => postF tt (withNextPc newPC mach)
    | LoadByte ctxid a => fun postF postA => load 1 ctxid a mach postF
    | LoadHalf ctxid a => fun postF postA => load 2 ctxid a mach postF
    | LoadWord ctxid a => fun postF postA => load 4 ctxid a mach postF
    | LoadDouble ctxid a => fun postF postA => load 8 ctxid a mach postF
    | StoreByte ctxid a v => fun postF postA => store 1 ctxid a v mach (postF tt)
    | StoreHalf ctxid a v => fun postF postA => store 2 ctxid a v mach (postF tt)
    | StoreWord ctxid a v => fun postF postA => store 4 ctxid a v mach (postF tt)
    | StoreDouble ctxid a v => fun postF postA => store 8 ctxid a v mach (postF tt)
    | EndCycleNormal => fun postF postA => postF tt (updatePc mach)
    | EndCycleEarly _ => fun postF postA => postA (updatePc mach) (* ignores postF containing the continuation *)
    | MakeReservation _
    | ClearReservation _
    | CheckReservation _
    | GetCSRField _
    | SetCSRField _ _
    | GetPrivMode
    | SetPrivMode _
    | Fence _ _
        => fun postF postA => False
    end.

  Definition no_M(mach: RiscvMachine): Prop :=
      forall a v, isXAddr4 a mach.(getXAddrs) ->
        Memory.load_bytes 4 mach.(getMem) a = Some v ->
        forall minst, decode RV32IM (LittleEndian.combine 4 v) <> MInstruction minst.

  Instance MinimalNoMulPrimitivesParams:
    PrimitivesParams (free riscv_primitive primitive_result) RiscvMachine :=
  {|
    Primitives.mcomp_sat A m mach postF :=
      @free.interpret _ _ _ interpret_action A m mach postF (fun _ => False);
    Primitives.is_initial_register_value x := True;
    Primitives.nonmem_load _ _ _ _ _ := False;
    Primitives.nonmem_store _ _ _ _ _ _ := False;
    Primitives.valid_machine := no_M;
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

  Lemma interpret_action_weaken_post a (postF1 postF2: _ -> _ -> Prop) (postA1 postA2: _ -> Prop):
    (forall r s, postF1 r s -> postF2 r s) ->
    (forall s, postA1 s -> postA2 s) ->
    forall s, interpret_action a s postF1 postA1 -> interpret_action a s postF2 postA2.
  Proof.
    destruct a; cbn; try solve [intuition eauto].
    all : eauto using load_weaken_post, store_weaken_post.
  Qed.

  Global Instance MinimalNoMulSatisfies_mcomp_sat_spec: mcomp_sat_spec MinimalNoMulPrimitivesParams.
  Proof.
    split; cbv [mcomp_sat MinimalNoMulPrimitivesParams Bind Return Monad_free].
    { symmetry. eapply interpret_bind_ex_mid, interpret_action_weaken_post. }
    { symmetry; intros. rewrite interpret_ret; eapply iff_refl. }
  Qed.

  Lemma preserve_undef_on{memOk: map.ok Mem}: forall n (m m': Mem) a w s,
      Memory.store_bytes n m a w = Some m' ->
      map.undef_on m s ->
      map.undef_on m' s.
  Proof.
    eauto using map.same_domain_preserves_undef_on, Memory.store_bytes_preserves_domain.
  Qed.

  Lemma transfer_load4bytes_to_previous_mem: forall (a: word) v n m m' r w someSet,
      Memory.store_bytes n m r w = Some m' ->
      (* a notin r..r+n *)
      isXAddr4 a (invalidateWrittenXAddrs n r someSet) ->
      Memory.load_bytes 4 m' a = Some v ->
      Memory.load_bytes 4 m a = Some v.
  Proof.
  Admitted.

  Lemma isXAddr4_uninvalidate: forall (a: word) n r xa,
      isXAddr4 a (invalidateWrittenXAddrs n r xa) ->
      isXAddr4 a xa.
  Proof.
  Admitted.

  Lemma interpret_action_total{memOk: map.ok Mem} a s postF postA :
    no_M s ->
    interpret_action a s postF postA ->
    exists s', no_M s' /\ (postA s' \/ exists v', postF v' s').
  Proof.
    destruct s, a; cbn -[HList.tuple Memory.load_bytes invalidateWrittenXAddrs];
      cbv [load store no_M]; cbn -[HList.tuple Memory.load_bytes invalidateWrittenXAddrs];
        repeat destruct_one_match;
        intuition idtac;
        repeat lazymatch goal with
               | H : postF _ ?mach |- exists _ : RiscvMachine, _ =>
                 exists mach; cbn [RiscvMachine.getMem RiscvMachine.getXAddrs]
               | H : postA ?mach |- exists _ : RiscvMachine, _ =>
                 exists mach; cbn [RiscvMachine.getMem RiscvMachine.getXAddrs]
               | Hexists : (exists v, ?P), Hforall : (forall v, ?P -> _) |- _ =>
                 let v := fresh "v" in
                 destruct Hexists as [v Hexists];
                   specialize (Hforall v Hexists)
               end;
        ssplit; eauto; cbn -[HList.tuple Memory.load_bytes invalidateWrittenXAddrs];
        change removeXAddr with (@List.removeb word word.eqb);
        rewrite ?ListSet.of_list_removeb;
        intuition eauto 10 using transfer_load4bytes_to_previous_mem, isXAddr4_uninvalidate.
  Qed.

  Lemma interpret_action_total'{memOk: map.ok Mem} a s post :
    no_M s ->
    interpret_action a s post (fun _ : RiscvMachine => False) ->
    exists v s', post v s' /\ no_M s'.
  Proof.
    intros. pose proof interpret_action_total as P.
    specialize P with (postA := (fun _ : RiscvMachine => False)). simpl in P.
    specialize (P _ _ _ H H0).
    destruct P as (s' & ? & ?).
    destruct H2 as [[] | (v' & ?)].
    eauto.
  Qed.

  Import coqutil.Tactics.Tactics.

  Lemma interpret_action_appendonly a s postF postA :
    interpret_action a s postF postA ->
    interpret_action a s (fun _ s' => endswith s'.(getLog) s.(getLog))
                           (fun s' => endswith s'.(getLog) s.(getLog)).
  Proof.
    destruct s, a; cbn; cbv [load store nonmem_load nonmem_store]; cbn;
      repeat destruct_one_match;
      intuition eauto using endswith_refl, endswith_cons_l.
  Qed.

  (* NOTE: maybe instead a generic lemma to push /\ into postcondition? *)
  Lemma interpret_action_appendonly' a s postF postA :
    interpret_action a s postF postA ->
    interpret_action a s (fun v s' => postF v s' /\ endswith s'.(getLog) s.(getLog))
                         (fun   s' => postA   s' /\ endswith s'.(getLog) s.(getLog)).
  Proof.
    destruct s, a; cbn; cbv [load store nonmem_load nonmem_store]; cbn;
      repeat destruct_one_match; intros; destruct_products; try split;
        intuition eauto using endswith_refl, endswith_cons_l.
  Qed.

  Lemma interpret_action_appendonly'' a s post :
    interpret_action a s post (fun _ : RiscvMachine => False) ->
    interpret_action a s (fun v s' => post v s' /\ endswith s'.(getLog) s.(getLog))
                         (fun _ : RiscvMachine => False).
  Proof.
    intros. pose proof interpret_action_appendonly' as P.
    specialize (P _ _ _ (fun _ : RiscvMachine => False) H). simpl in P.
    eapply interpret_action_weaken_post. 3: exact P. all: simpl; intuition eauto.
  Qed.

  Lemma interpret_action_preserves_valid{memOk: map.ok Mem} a s postF postA :
    no_M s ->
    interpret_action a s postF postA ->
    interpret_action a s (fun v s' => postF v s' /\ no_M s')
                         (fun s' => postA s' /\ no_M s').
  Proof.
    destruct s, a; cbn; cbv [load store no_M];
      cbn -[HList.tuple Memory.load_bytes invalidateWrittenXAddrs];
      repeat destruct_one_match; intros; destruct_products; try split;
        change removeXAddr with (@List.removeb word word.eqb);
        rewrite ?ListSet.of_list_removeb;
        intuition eauto 10 using transfer_load4bytes_to_previous_mem, isXAddr4_uninvalidate.
  Qed.

  Lemma interpret_action_preserves_valid'{memOk: map.ok Mem} a s post :
    no_M s ->
    interpret_action a s post (fun _ : RiscvMachine => False) ->
    interpret_action a s (fun v s' => post v s' /\ no_M s')
                         (fun _ : RiscvMachine => False).
  Proof.
    intros. pose proof interpret_action_preserves_valid as P.
    specialize (P _ _ _ (fun _ : RiscvMachine => False) H H0). simpl in P.
    eapply interpret_action_weaken_post. 3: exact P. all: simpl; intuition eauto.
  Qed.

  Global Instance MinimalNoMulPrimitivesSane{memOk: map.ok Mem} :
    PrimitivesSane MinimalNoMulPrimitivesParams.
  Proof.
    split; cbv [mcomp_sane valid_machine MinimalNoMulPrimitivesParams]; intros *; intros D M;
      (split; [ exact (interpret_action_total' _ st _ D M)
              | eapply interpret_action_preserves_valid'; try eassumption;
                eapply interpret_action_appendonly''; try eassumption ]).
  Qed.

  Global Instance MinimalNoMulSatisfiesPrimitives{memOk: map.ok Mem} :
    Primitives MinimalNoMulPrimitivesParams.
  Proof.
    split; try exact _.
    all : cbv [mcomp_sat spec_load spec_store MinimalNoMulPrimitivesParams invalidateWrittenXAddrs].
    all: intros;
      repeat match goal with
      | _ => progress subst
      | _ => Option.inversion_option
      | _ => progress cbn -[Memory.load_bytes Memory.store_bytes HList.tuple]
      | _ => progress cbv [valid_register is_initial_register_value load store Memory.loadByte Memory.loadHalf Memory.loadWord Memory.loadDouble Memory.storeByte Memory.storeHalf Memory.storeWord Memory.storeDouble] in *
      | H : exists _, _ |- _ => destruct H
      | H : _ /\ _ |- _ => destruct H
      | |- _ => solve [ intuition (eauto || blia) ]
      | H : _ \/ _ |- _ => destruct H
      | |- context[match ?x with _ => _ end] => destruct x eqn:?
      | |-_ /\ _ => split
      end.
      (* setRegister *)
      destruct initialL; eassumption.
  Qed.

End Riscv.
