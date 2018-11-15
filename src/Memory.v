Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Require Import bbv.ZLib.
Require Import riscv.util.Word.
Require Export riscv.util.ListLib.
Require Import riscv.util.div_mod_to_quot_rem.
Require Import riscv.util.Tactics.
Require Import riscv.Utility.

Local Open Scope Z_scope.

Section ValidAddr.

Context {t: Set}.
Context {MW: MachineWidth t}.

Definition valid_addr(addr: t)(alignment size: Z): Prop :=
  regToZ_unsigned addr + alignment <= size /\ (regToZ_unsigned addr) mod alignment = 0.

(* Note: alignment refers to addr, not to the range *)
Definition in_range(addr: t)(alignment start size: Z): Prop :=
  start <= regToZ_unsigned addr /\
  regToZ_unsigned addr + alignment <= start + size /\
  regToZ_unsigned addr mod alignment = 0.

Definition not_in_range(addr: t)(alignment start size: Z): Prop :=
  regToZ_unsigned addr + alignment <= start \/ start + size <= regToZ_unsigned addr.

Definition valid_addr'(addr: t)(alignment size: Z): Prop :=
  in_range addr alignment 0 size.

Lemma valid_addr_alt: forall (addr: t) alignment size,
    valid_addr addr alignment size <-> valid_addr' addr alignment size.
Proof.
  intros. unfold valid_addr, valid_addr', in_range.
  pose proof (regToZ_unsigned_bounds addr).
  intuition omega.
Qed.

End ValidAddr.

Class MemoryFunctions(t: Set)`{MachineWidth t} := mkMemoryFunctions {
  Mem: Type;

  memSize: Mem -> Z;

  loadByte   : Mem -> t -> word  8;
  loadHalf   : Mem -> t -> word 16;
  loadWord   : Mem -> t -> word 32;
  loadDouble : Mem -> t -> word 64;
  storeByte  : Mem -> t -> word  8 -> Mem;
  storeHalf  : Mem -> t -> word 16 -> Mem;
  storeWord  : Mem -> t -> word 32 -> Mem;
  storeDouble: Mem -> t -> word 64 -> Mem;

  memSize_bound: forall m,
    memSize m <= 2^XLEN;

  memSize_mod8: forall m,
    memSize m mod 8 = 0;

  loadStoreByte_eq: forall m (a1 a2: t) v,
    valid_addr a1 1 (memSize m) ->
    a2 = a1 ->
    loadByte (storeByte m a1 v) a2 = v;

  loadStoreByte_ne: forall m (a1 a2: t) v,
    valid_addr a1 1 (memSize m) ->
    valid_addr a2 1 (memSize m) ->
    a2 <> a1 ->
    loadByte (storeByte m a1 v) a2 = loadByte m a2;

  storeByte_preserves_memSize: forall m (a: t) v,
    memSize (storeByte m a v) = memSize m;

  loadStoreHalf_eq: forall m (a1 a2: t) v,
    valid_addr a1 2 (memSize m) ->
    a2 = a1 ->
    loadHalf (storeHalf m a1 v) a2 = v;

  loadStoreHalf_ne: forall m (a1 a2: t) v,
    valid_addr a1 2 (memSize m) ->
    valid_addr a2 2 (memSize m) ->
    a2 <> a1 ->
    loadHalf (storeHalf m a1 v) a2 = loadHalf m a2;

  storeHalf_preserves_memSize: forall m (a: t) v,
    memSize (storeHalf m a v) = memSize m;

  loadStoreWord_eq: forall m (a1 a2: t) v,
    valid_addr a1 4 (memSize m) ->
    a2 = a1 ->
    loadWord (storeWord m a1 v) a2 = v;

  loadStoreWord_ne: forall m (a1 a2: t) v,
    valid_addr a1 4 (memSize m) ->
    valid_addr a2 4 (memSize m) ->
    a2 <> a1 ->
    loadWord (storeWord m a1 v) a2 = loadWord m a2;

  storeWord_preserves_memSize: forall m (a: t) v,
    memSize (storeWord m a v) = memSize m;

  loadStoreDouble_eq: forall m (a1 a2: t) v,
    valid_addr a1 8 (memSize m) ->
    a2 = a1 ->
    loadDouble (storeDouble m a1 v) a2 = v;

  loadStoreDouble_ne: forall m (a1 a2: t) v,
    valid_addr a1 8 (memSize m) ->
    valid_addr a2 8 (memSize m) ->
    a2 <> a1 ->
    loadDouble (storeDouble m a1 v) a2 = loadDouble m a2;

  storeDouble_preserves_memSize: forall m (a: t) v,
    memSize (storeDouble m a v) = memSize m;

  loadHalf_spec: forall m a,
    valid_addr a 2 (memSize m) ->
    loadHalf m a = wappend (loadByte m (add a (ZToReg 1))) (loadByte m a);

  loadWord_spec: forall m a,
    valid_addr a 4 (memSize m) ->
    loadWord m a = wappend (loadHalf m (add a (ZToReg 2))) (loadHalf m a);

  loadDouble_spec: forall m a,
    valid_addr a 8 (memSize m) ->
    loadDouble m a = wappend (loadWord m (add a (ZToReg 4))) (loadWord m a);

  (* Note: No storeHalf_spec, storeWord_spec, storeDouble_spec, because we don't
     want to compare memories with = (too restrictive for implementors), nor start
     using a custom equivalence (too complicated).
     Also, it shouldn't be needed, because at the end you only need to know what
     you get back when you do a load, and you can split a load into the unit on
     which the store was done. *)
}.

Arguments Mem _ {_} {_}.


Lemma valid_addr_8_4: forall {t: Set} {MW: MachineWidth t} (addr: t) size,
    valid_addr addr 8 size ->
    valid_addr addr 4 size.
Proof.
  intros. unfold valid_addr in *.
  intuition (try omega).
  div_mod_to_quot_rem.
  nia.
Qed.

Ltac demod :=
  repeat match goal with
         | H: _ mod _ = 0 |- _ => apply Nat.mod_divides in H; [destruct H | congruence]
         end.

Ltac destruct_list_length :=
  match goal with
  | _: context [Zlength ?L] |- _ =>
       is_var L;
       destruct (destruct_list_length _ L) as [ ? | ? ]; [ subst L | ]
  end.

Ltac regOmega_pre := apply regToZ_unsigned_eq || apply regToZ_unsigned_ne.

Ltac regOmega := regOmega_pre; omega.

(*
Hint Rewrite
     Nat.succ_inj_wd
     Nat.mul_0_r
     Nat.add_0_r
     mod_add_r
     mul_div_exact
using omega
: nats.
 *)

Ltac pose_mem_proofs :=
  repeat match goal with
         | m: _ |- _ => unique pose proof (memSize_bound m)
         | m: _ |- _ => unique pose proof (memSize_mod8 m)
         | H: valid_addr _ 8 _ |- _ => unique pose proof (valid_addr_8_4 _ _ H)
         end.

Ltac pose_regToZ_unsigned_bounds :=
  repeat so fun hyporgoal => match hyporgoal with
  | context [regToZ_unsigned ?a] => unique pose proof (regToZ_unsigned_bounds a)
  end.

Hint Rewrite
     @regToZ_ZToReg_unsigned
     using omega
  : rew_MachineWidth.
Hint Rewrite
     @add_def_unsigned
     @sub_def_unsigned
     @mul_def_unsigned
     @regToZ_unsigned_four
     @ZToReg_regToZ_unsigned
  : rew_MachineWidth.

Hint Rewrite mod_add_r using omega : rew_Z.
Hint Rewrite <- Zdiv.Z_div_exact_2 using (rewrite? sub_mod_0; omega) : rew_Z.
Hint Rewrite Z.mul_0_r Z.add_0_r Zplus_minus : rew_Z.
Hint Rewrite @storeWord_preserves_memSize : rew_mem.

Ltac subst_0_Z :=
  repeat match goal with
         | i: Z |- _ => assert (i = 0) by omega; subst i
         end.

Ltac mem_sideconditions :=
  unfold valid_addr in *;
  pose_mem_proofs;
  pose_regToZ_unsigned_bounds;
  try regOmega_pre;
  subst_0_Z;
  (* We can't use autorewrite because when a subterm has the right shape for rewriting,
     but solving the sideconditions fails, autorewrite does not backtrack to the next
     subterm, but just stops: *)
  repeat autorewrite with rew_Zlist rew_MachineWidth rew_Z rew_mem in *;
  (* to emulate "rewrite_strat in *", in such a way that the side condition solvers can use
     all other hypotheses (so we only revert on hyp at a time)
  repeat match goal with
         | H: _ |- _ =>
           progress (
               revert H;
               (rewrite_strat (topdown
                                 (choice (choice (hints rew_Zlist) (hints rew_MachineWidth))
                                         (choice (hints rew_Z) (hints rew_mem)))));
               intro H
             )
         end;
  *)
  try reflexivity;
  try solve [repeat ((try omega); f_equal)];
  try (solve [div_mod_to_quot_rem; nia]).

Ltac mem_simpl :=
  pose_mem_proofs;
  unfold valid_addr in *;
  try regOmega_pre;
  repeat (
      autorewrite with nats in *;
      rewrite? storeWord_preserves_memSize in *;
      rewrite? loadDouble_spec by mem_simpl;
      rewrite? loadStoreWord_ne by mem_simpl;
      rewrite? loadStoreWord_eq by mem_simpl;
      subst;
      auto
    );
  try solve [repeat ((try omega); f_equal)].


Section MemoryHelpers.

  Context {t: Set}.
  Context {MW: MachineWidth t}.
  Context {MF: MemoryFunctions t}.

  Add Ring tring: (@regRing t MW).

  Lemma regToZ_unsigned_add: forall a b,
      0 <= regToZ_unsigned a + regToZ_unsigned b < 2 ^ XLEN ->
      regToZ_unsigned (add a b) = regToZ_unsigned a + regToZ_unsigned b.
  Proof.
    intros.
    rewrite add_def_unsigned.
    apply regToZ_ZToReg_unsigned in H.
    exact H.
  Qed.

  Lemma regToZ_unsigned_add_l: forall (a: Z) (b: t),
      0 <= a ->
      0 <= a + regToZ_unsigned b < 2 ^ XLEN ->
      regToZ_unsigned (add (ZToReg a) b) = a + regToZ_unsigned b.
  Proof.
    intros.
    pose proof (regToZ_unsigned_bounds b).
    rewrite regToZ_unsigned_add.
    - rewrite regToZ_ZToReg_unsigned by omega. reflexivity.
    - rewrite regToZ_ZToReg_unsigned; omega.
  Qed.

  Lemma regToZ_unsigned_add_r: forall (a: t) (b: Z),
      0 <= b ->
      0 <= regToZ_unsigned a + b < 2 ^ XLEN ->
      regToZ_unsigned (add a (ZToReg b)) = regToZ_unsigned a + b.
  Proof.
    intros.
    pose proof (regToZ_unsigned_bounds a).
    rewrite regToZ_unsigned_add.
    - rewrite regToZ_ZToReg_unsigned by omega. reflexivity.
    - rewrite regToZ_ZToReg_unsigned; omega.
  Qed.

  Lemma loadWord_storeDouble_ne: forall m (a1 a2: t) v,
      valid_addr a1 8 (memSize m) ->
      valid_addr a2 4 (memSize m) ->
      a2 <> a1 ->
      a2 <> add a1 (ZToReg 4) ->
      loadWord (storeDouble m a1 v) a2 = loadWord m a2.
  Proof.
    intros.
    pose proof (memSize_bound m) as B.
    pose proof loadStoreDouble_ne as P.
    specialize P with (1 := H).
    destruct (ZLib.mod2_cases (regToZ_unsigned a2 / 4)) as [C | C].
    - specialize (P a2 v).
      assert (valid_addr a2 8 (memSize m)) as V. {
        unfold valid_addr in *.
        destruct H, H0.
        assert (regToZ_unsigned a2 mod 8 = 0). {
          apply Z.mod_divide; try congruence.
          change 8 with (2 * 4).
          replace (regToZ_unsigned a2) with (regToZ_unsigned a2 / 4 * 4).
          - apply Z.mul_divide_mono_r.
            apply Z.mod_divide; congruence.
          - apply ZLib.div_mul_undo; congruence.
        }
        split; try assumption.
        pose proof (memSize_mod8 m).
        div_mod_to_quot_rem. omega.
      }
      specialize (P V).
      rewrite loadDouble_spec in P
        by (rewrite storeDouble_preserves_memSize; assumption).
      specialize (P H1).
      rewrite loadDouble_spec in P by assumption.
      pose proof (@wappend_inj 32 32) as Q.
      specialize Q with (3 := P).
      destruct Q as [_ Q]; [omega..|assumption].
    - specialize (P (sub a2 (ZToReg 4)) v).
      pose proof (regToZ_unsigned_bounds a2).
      assert (regToZ_unsigned a2 = 0 \/
              regToZ_unsigned a2 = 1 \/
              regToZ_unsigned a2 = 2 \/
              regToZ_unsigned a2 = 3 \/
              4 <= regToZ_unsigned a2) as D by omega.
      destruct D as [D | [D | [D | [D | D]]]];
        [ (rewrite D in C; simpl in C; discriminate) .. | ].
      pose proof (loadDouble_spec              m       (sub a2 (ZToReg 4))) as Sp1.
      pose proof (loadDouble_spec (storeDouble m a1 v) (sub a2 (ZToReg 4))) as Sp2.
      unfold valid_addr in *.
      destruct H, H0.
      rewrite storeDouble_preserves_memSize in Sp2.
      replace (regToZ_unsigned  (sub a2 (ZToReg 4))) with (regToZ_unsigned a2 - 4) in *.
      + assert ((regToZ_unsigned a2 - 4) mod 8 = 0) as X. {
          clear Sp1 Sp2 P.
          div_mod_to_quot_rem. nia.
        }
        assert (regToZ_unsigned a2 - 4 + 8 <= memSize m) as A by omega.
        specialize (P (conj A X)).
        rewrite Sp1 in P by (split; assumption). clear Sp1.
        rewrite Sp2 in P by (split; assumption). clear Sp2.
        assert (sub a2 (ZToReg 4) <> a1) as Ne. {
          clear -H2.
          intro. subst. apply H2.
          ring.
        }
        specialize (P Ne).
        pose proof (@wappend_inj 32 32) as Q.
        specialize Q with (3 := P).
        destruct Q as [Q _]; try omega.
        ring_simplify (add (sub a2 (ZToReg 4)) (ZToReg 4)) in Q.
        assumption.
      + rewrite sub_def_unsigned.
        rewrite regToZ_unsigned_four.
        rewrite regToZ_ZToReg_unsigned; omega.
  Qed.

  Lemma loadWord_storeDouble_ne': forall (m : Mem t) (a1 a2 : t) (v : word 64),
      in_range a1 8 0 (memSize m) ->
      in_range a2 4 0 (memSize m) ->
      (* a2 (4 bytes big) is not in the 8-byte range starting at a1 *)
      not_in_range a2 4 (regToZ_unsigned a1) 8 ->
      loadWord (storeDouble m a1 v) a2 = loadWord m a2.
  Proof.
    intros.
    pose proof (memSize_bound m).
    apply loadWord_storeDouble_ne;
    unfold in_range, not_in_range, valid_addr in *;
    simpl in *;
    intuition (subst; try omega);
    rewrite @add_def_unsigned in *;
    rewrite @regToZ_unsigned_four in *;
    rewrite @regToZ_ZToReg_unsigned in * by omega;
    omega.
  Qed.

  Definition store_byte_list(l: list (word 8))(a: t)(m: Mem t): Mem t :=
    fold_left_index (fun i m w => storeByte m (add a (ZToReg i)) w) l 0 m.

  Definition load_byte_list(m: Mem t)(start: t)(count: Z): list (word 8) :=
    map_range (fun i => loadByte m (add start (ZToReg i))) count.

  Definition store_half_list(l: list (word 16))(a: t)(m: Mem t): Mem t :=
    fold_left_index (fun i m w => storeHalf m (add a (ZToReg (2 * i))) w) l 0 m.

  Definition load_half_list(m: Mem t)(start: t)(count: Z): list (word 16) :=
    map_range (fun i => loadHalf m (add start (ZToReg (2 * i)))) count.

  Definition store_word_list(l: list (word 32))(a: t)(m: Mem t): Mem t :=
    fold_left_index (fun i m w => storeWord m (add a (ZToReg (4 * i))) w) l 0 m.

  Definition load_word_list(m: Mem t)(start: t)(count: Z): list (word 32) :=
    map_range (fun i => loadWord m (add start (ZToReg (4 * i)))) count.

  Definition store_double_list(l: list (word 64))(a: t)(m: Mem t): Mem t :=
    fold_left_index (fun i m w => storeDouble m (add a (ZToReg (4 * i))) w) l 0 m.

  Definition load_double_list(m: Mem t)(start: t)(count: Z): list (word 64) :=
    map_range (fun i => loadDouble m (add start (ZToReg (8 * i)))) count.

  Lemma Znth_error_load_word_list: forall m l i offset,
      0 <= i < l ->
      Znth_error (load_word_list m offset l) i =
      Some (loadWord m (add offset (ZToReg (4 * i)))).
  Proof.
    intros. unfold load_word_list.
    rewrite Znth_error_map_range by assumption.
    reflexivity.
  Qed.

  Lemma Zlength_load_word_list: forall m l offset,
      0 <= l ->
      Zlength (load_word_list m offset l) = l.
  Proof.
    intros. unfold load_word_list.
    apply Zlength_map_range.
    assumption.
  Qed.

  Local Arguments Z.mul: simpl never.

  Lemma fold_left_index_cons': forall T R (a: T) (l: list T) (f: Z -> R -> T -> R) (i: Z) (r: R),
      fold_left_index f (a :: l) i r = fold_left_index f l (i + 1) (f i r a).
  Proof.
    intros. reflexivity.
  Qed.

  Lemma fold_left_index_shift: forall T R (l: list T) (f: Z -> R -> T -> R) (i d: Z) (r: R),
      fold_left_index f l (i + d) r = fold_left_index (fun j => f (j + d)) l i r.
  Proof.
    induction l; intros.
    - reflexivity.
    - unfold fold_left_index in *. simpl in *.
      replace (i + d + 1) with (i + 1 + d) by omega.
      apply IHl.
  Qed.

  Lemma fold_left_index_cons: forall T R (a: T) (l: list T) (f: Z -> R -> T -> R) (i: Z) (r: R),
      fold_left_index f (a :: l) i r =
      fold_left_index (fun i => f (i + 1)) l i (f i r a).
  Proof.
    intros. rewrite fold_left_index_cons'. apply fold_left_index_shift.
  Qed.

  Lemma fold_left_ext: forall A B (f1 f2: A -> B -> A) (l: list B) (a0: A),
      (forall a b, f1 a b = f2 a b) ->
      fold_left f1 l a0 = fold_left f2 l a0.
  Proof.
    induction l; intros.
    - reflexivity.
    - simpl. rewrite H. apply IHl. assumption.
  Qed.

  Lemma map_nat_range_shift: forall R (f: nat -> R) (count start d: nat),
      map_nat_range f (start + d) count = map_nat_range (fun j => f (j + d)%nat) start count.
  Proof.
    induction count; intros.
    - reflexivity.
    - unfold map_nat_range in *.
      f_equal.
      simpl.
      change (S (start + d))%nat with (S start + d)%nat.
      apply IHcount.
  Qed.

  Lemma map_nat_range_ext: forall R (f1 f2: nat -> R) (count start: nat),
      (forall a, Z.of_nat start <= Z.of_nat a < Z.of_nat start + Z.of_nat count -> f1 a = f2 a) ->
      map_nat_range f1 start count = map_nat_range f2 start count.
  Proof.
    induction count; intros.
    - reflexivity.
    - simpl. f_equal.
      + apply H. lia.
      + apply IHcount. intros. apply H. lia.
  Qed.

  Lemma store_word_list_cons: forall w l a m,
      store_word_list (w :: l) a m = store_word_list l (add a (ZToReg 4)) (storeWord m a w).
  Proof.
    intros. unfold store_word_list. rewrite fold_left_index_cons.
    rewrite Z.mul_0_r.
    ring_simplify (add a (ZToReg 0)).
    unfold fold_left_index.
    f_equal.
    apply fold_left_ext.
    intros. do 2 f_equal.
    rewrite! add_def_unsigned.
    rewrite! regToZ_unsigned_four.
    rewrite! ZToReg_morphism.(morph_mul).
    rewrite! ZToReg_morphism.(morph_add).
    rewrite! ZToReg_regToZ_unsigned.
    ring.
  Qed.

  Lemma store_word_list_nil: forall a m,
      store_word_list nil a m = m.
  Proof. intros. reflexivity. Qed.

  Lemma store_word_list_preserves_memSize_aux: forall ll (m: Mem t) a l,
      length l = ll ->
      memSize (store_word_list l a m) = memSize m.
  Proof.
    induction ll; intros; subst; destruct l; simpl in *; try reflexivity; try congruence.
    inversion H; subst.
    rewrite store_word_list_cons.
    rewrite IHll by reflexivity.
    apply storeWord_preserves_memSize.
  Qed.

  Lemma store_word_list_preserves_memSize: forall (m: Mem t) l a,
      memSize (store_word_list l a m) = memSize m.
  Proof.
    intros. eapply store_word_list_preserves_memSize_aux. reflexivity.
  Qed.

  Lemma loadWord_before_store_word_list: forall l (m: Mem t) (a1 a2: t),
      regToZ_unsigned a1 + 4 <= regToZ_unsigned a2 ->
      regToZ_unsigned a2 + 4 * (Zlength l) <= (memSize m) ->
      valid_addr a1 4 (memSize m) ->
      valid_addr a2 4 (memSize m) ->
      loadWord (store_word_list l a2 m) a1 = loadWord m a1.
  Proof.
    induction l; intros; simpl in *; try reflexivity.
    rewrite store_word_list_cons.
    destruct_list_length.
    - rewrite store_word_list_nil.
      rewrite loadStoreWord_ne; mem_sideconditions.
    - rewrite IHl by mem_sideconditions.
      rewrite loadStoreWord_ne; mem_sideconditions.
  Qed.

  Lemma loadWord_after_store_word_list: forall l (m: Mem t) (a1 a2: t),
      regToZ_unsigned a2 + 4 * (Zlength l) <= regToZ_unsigned a1 ->
      valid_addr a1 4 (memSize m) ->
      valid_addr a2 4 (memSize m) ->
      loadWord (store_word_list l a2 m) a1 = loadWord m a1.
  Proof.
    induction l; intros; simpl in *; try reflexivity.
    rewrite store_word_list_cons.
    destruct_list_length.
    - rewrite store_word_list_nil.
      rewrite loadStoreWord_ne; mem_sideconditions.
    - rewrite IHl by mem_sideconditions.
      rewrite loadStoreWord_ne; mem_sideconditions.
  Qed.

  Lemma loadWord_outside_store_word_list: forall l (m: Mem t) a1 a2,
      not_in_range a1 4 (regToZ_unsigned a2) (4 * Zlength l) ->
      regToZ_unsigned a2 + 4 * Zlength l <= memSize m ->
      valid_addr a1 4 (memSize m) ->
      valid_addr a2 4 (memSize m) ->
      loadWord (store_word_list l a2 m) a1 = loadWord m a1.
  Proof.
    intros. unfold not_in_range in *. destruct H.
    - apply loadWord_before_store_word_list; mem_sideconditions.
    - apply loadWord_after_store_word_list; mem_sideconditions.
  Qed.

  Local Arguments Nat.div: simpl never.
  Local Arguments nth: simpl never.

  Lemma loadWord_inside_store_word_list_aux: forall l (m: Mem t) i offset,
      0 <= i < Zlength l ->
      regToZ_unsigned offset + 4 * Zlength l <= memSize m ->
      valid_addr offset 4 (memSize m) ->
      Some (loadWord (store_word_list l offset m) (ZToReg (regToZ_unsigned offset + 4 * i))) =
      Znth_error l i.
  Proof.
    induction l; intros; unfold in_range in *; simpl in *; mem_sideconditions.
    rewrite store_word_list_cons.
    destruct_list_length; simpl in *.
    - rewrite store_word_list_nil.
      rewrite loadStoreWord_eq by mem_sideconditions.
      assert (i = 0) by omega. subst.
      reflexivity.
    - assert (i = 0 \/ 0 < i) as C by omega.
      destruct C as [C | C].
      + rewrite loadWord_before_store_word_list; mem_sideconditions.
        rewrite loadStoreWord_eq by mem_sideconditions.
        reflexivity.
      + mem_sideconditions.
        specialize (IHl (storeWord m offset a) (i - 1) (add offset (ZToReg 4))).
        rewrite <- IHl; mem_sideconditions.
  Qed.

  Lemma loadWord_inside_store_word_list: forall l (m: Mem t) addr offset,
      in_range addr 4 (regToZ_unsigned offset) (4 * Zlength l) ->
      regToZ_unsigned offset + 4 * Zlength l <= memSize m ->
      valid_addr offset 4 (memSize m) ->
      Some (loadWord (store_word_list l offset m) addr) =
      Znth_error l (regToZ_unsigned (sub addr offset) / 4).
  Proof.
    intros. unfold in_range in *.
    rewrite <- (loadWord_inside_store_word_list_aux l m
                         (regToZ_unsigned (sub addr offset) / 4) offset);
      mem_sideconditions.
  Qed.

  Lemma loadDouble_before_store_word_list: forall l (m: Mem t) (a1 a2: t),
      regToZ_unsigned a1 + 8 <= regToZ_unsigned a2 ->
      regToZ_unsigned a2 + 4 * (Zlength l) <= (memSize m) ->
      valid_addr a1 8 (memSize m) ->
      valid_addr a2 4 (memSize m) ->
      loadDouble (store_word_list l a2 m) a1  = loadDouble m a1.
  Proof.
    induction l; intros; simpl in *; mem_sideconditions.
    destruct_list_length; simpl in *; mem_sideconditions.
    - rewrite store_word_list_cons.
      rewrite store_word_list_nil.
      rewrite? loadDouble_spec by mem_sideconditions.
      rewrite? loadStoreWord_ne by mem_sideconditions.
      reflexivity.
    - rewrite store_word_list_cons.
      rewrite IHl by  mem_sideconditions.
      rewrite? loadDouble_spec by mem_sideconditions.
      rewrite? loadStoreWord_ne by mem_sideconditions.
      reflexivity.
  Qed.

  Lemma loadDouble_after_store_word_list: forall l (m: Mem t) (a1 a2: t),
      regToZ_unsigned a2 + 4 * (Zlength l) <= regToZ_unsigned a1 ->
      valid_addr a1 8 (memSize m) ->
      valid_addr a2 4 (memSize m) ->
      loadDouble (store_word_list l a2 m) a1  = loadDouble m a1.
  Proof.
    induction l; intros; simpl in *; mem_sideconditions.
    destruct_list_length; simpl in *; mem_sideconditions.
    - rewrite store_word_list_cons.
      rewrite store_word_list_nil.
      rewrite? loadDouble_spec by mem_sideconditions.
      rewrite? loadStoreWord_ne by mem_sideconditions.
      reflexivity.
    - rewrite store_word_list_cons.
      rewrite IHl by  mem_sideconditions.
      rewrite? loadDouble_spec by mem_sideconditions.
      rewrite? loadStoreWord_ne by mem_sideconditions.
      reflexivity.
  Qed.

  Lemma loadDouble_outside_store_word_list: forall l (m: Mem t) a1 a2,
      not_in_range a1 8 (regToZ_unsigned a2) (4 * Zlength l) ->
      regToZ_unsigned a2 + 4 * Zlength l <= memSize m ->
      valid_addr a1 8 (memSize m) ->
      valid_addr a2 4 (memSize m) ->
      loadDouble (store_word_list l a2 m) a1 = loadDouble m a1.
  Proof.
    intros. unfold not_in_range in *. destruct H.
    - apply loadDouble_before_store_word_list; mem_sideconditions.
    - apply loadDouble_after_store_word_list; mem_sideconditions.
  Qed.

  Lemma load_word_list_cons: forall l a m,
      valid_addr a 4 (memSize m) ->
      0 < l ->
      regToZ_unsigned a + 4 * l <= memSize m ->
      load_word_list m a l = loadWord m a :: load_word_list m (add a (ZToReg 4)) (l - 1).
  Proof.
    intros.
    unfold load_word_list at 1.
    unfold map_range.
    replace l with (Z.succ (l - 1)) by omega.
    rewrite Z2Nat.inj_succ by omega.
    rewrite map_nat_range_cons.
    mem_sideconditions.
    f_equal.
    unfold load_word_list, map_range.
    change 1%nat with (0 + 1)%nat.
    rewrite map_nat_range_shift.
    replace (Z.succ (l - 1) - 1) with (l - 1) by omega.
    apply map_nat_range_ext.
    intros.
    rewrite Nat2Z.inj_add.
    change (Z.of_nat 1) with 1.
    change (Z.of_nat 0) with 0 in *.
    rewrite Z2Nat.id in * by omega.
    f_equal.
    remember (Z.of_nat a0) as i; clear Heqi.
    mem_sideconditions.
    rewrite? regToZ_ZToReg_unsigned; try omega; mem_sideconditions.
  Qed.

  Lemma load_store_word_list_eq: forall l (m: Mem t) ll a1 a2,
      a2 = a1 ->
      ll = Zlength l ->
      regToZ_unsigned a1 mod 4 = 0 ->
      regToZ_unsigned a1 + 4 * (Zlength l) <= memSize m ->
      load_word_list (store_word_list l a1 m) a2 ll = l.
  Proof.
    induction l; intros; subst.
    - rewrite store_word_list_nil; mem_sideconditions.
    - destruct_list_length; mem_sideconditions.
      + mem_sideconditions.
        rewrite store_word_list_cons.
        rewrite store_word_list_nil.
        unfold load_word_list, map_range, map_nat_range. simpl.
        rewrite loadStoreWord_eq; mem_sideconditions.
        rewrite? regToZ_ZToReg_unsigned; mem_sideconditions.
      + rewrite store_word_list_cons.
        rewrite load_word_list_cons; mem_sideconditions.
        * rewrite loadWord_before_store_word_list; mem_sideconditions.
          rewrite loadStoreWord_eq by mem_sideconditions.
          replace (Zlength l + 1 - 1) with (Zlength l) by omega.
          specialize IHl with (ll := Zlength l).
          rewrite IHl; mem_sideconditions.
        * rewrite store_word_list_preserves_memSize.
          mem_sideconditions.
        * rewrite store_word_list_preserves_memSize.
          mem_sideconditions.
  Qed.

End MemoryHelpers.
