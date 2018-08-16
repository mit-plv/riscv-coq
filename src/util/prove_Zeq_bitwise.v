Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Require Import riscv.util.Tactics.
Require Import riscv.util.div_mod_to_quot_rem.
Require Import riscv.util.ZBitOps.
Require Export Coq.setoid_ring.ZArithRing.

Local Open Scope bool_scope.
Local Open Scope Z_scope.


Tactic Notation "safe_ring_simplify" constr(i) "in" ident(C) :=
  first [ring_simplify i in C |
         let t := type of i in fail 1000 "No ring structure found for" t ].

Lemma testbit_minus1: forall i,
    0 <= i ->
    Z.testbit (-1) i = true.
Proof.
  intros. rewrite (Z.bits_opp 1) by assumption.
  simpl. rewrite Z.bits_0. reflexivity. 
Qed.

Lemma testbit_above: forall {p n},
    0 <= n < 2 ^ p ->
    0 <= p ->
    forall i,
    p <= i ->
    Z.testbit n i = false.
Proof.
  intros.
  rewrite <- (Z.mod_small n (2 ^ p)) by assumption.
  apply Z.mod_pow2_bits_high.
  auto.
Qed.

Lemma if_same: forall (A: Type) (b: bool) (a: A),
    (if b then a else a) = a.
Proof.
  intros. destruct b; reflexivity.
Qed.

Lemma then_true_else_false: forall (b: bool),
    (if b then true else false) = b.
Proof.
  intros. destruct b; reflexivity.
Qed.

Hint Rewrite
     if_same
     then_true_else_false
     Bool.andb_false_r
     Bool.andb_true_r
     Bool.andb_false_l
     Bool.andb_true_l
     Bool.orb_false_r
     Bool.orb_true_r
     Bool.orb_false_l
     Bool.orb_true_l
     Bool.xorb_false_r
     Bool.xorb_true_r
     Bool.xorb_false_l
     Bool.xorb_true_l
  : bool_rewriting.

Ltac discard_contradictory_or t :=
  match goal with
  | |- ?P \/ ?Q => (assert (~P) as _ by t; right) || (assert (~Q) as _ by t; left)
  end.

Lemma testbit_if: forall (b: bool) n m i,
    Z.testbit (if b then n else m) i = if b then (Z.testbit n i) else (Z.testbit m i).
Proof.
  intros. destruct b; reflexivity.
Qed.

Lemma Zdiv_small_neg: forall a b,
    - b <= a < 0 ->
    a / b = -1.
Proof.
  intros. div_mod_to_quot_rem. nia.
Qed.

Lemma testbit_above_signed: forall l a i,
    - 2 ^ l <= a < 2 ^ l ->
    0 < l ->
    l < i ->
    Z.testbit a i = Z.testbit a l.
Proof.
  intros. destruct (Z.testbit a l) eqn: E.
  - rewrite Z.testbit_true in E by omega.
    assert (a < -1 \/ a = -1 \/ 0 <= a) as C by omega. destruct C as [C | [C | C]].
    + apply Z.bits_above_log2_neg; [omega|].
      rewrite (Z.pow_lt_mono_r_iff 2) by omega.
      pose proof (Z.log2_spec (Z.pred (- a))) as P.
      pose proof (Z.pow_lt_mono_r 2 l i).
      omega.
    + subst. apply testbit_minus1. omega.
    + rewrite Z.div_small in E by omega.
      cbv in E. discriminate.
  - assert (a < 0 \/ 0 <= a) as C by omega. destruct C as [C | C].
    + exfalso.
      pose proof (Z.testbit_true a l) as P.
      destruct P as [_ P]; [omega|].
      rewrite P in E; [discriminate|clear P E].
      rewrite Zdiv_small_neg by omega.
      reflexivity.
    + assert (a / 2 ^ i = 0) as F. {
        pose proof (Z.pow_lt_mono_r 2 l i).
        apply Z.div_small. omega.
      }
      rewrite Z.testbit_false by omega.
      rewrite F.
      reflexivity.
Qed.

Lemma testbit_above': forall n b i,
    0 <= n ->
    n < b ->
    0 <= Z.log2_up b ->
    Z.log2_up b <= i ->
    Z.testbit n i = false.
Proof.
  intros.
  pose proof (Z.log2_log2_up_spec b).
  apply (@testbit_above (Z.log2_up b) n); omega.
Qed.

Lemma testbit_above_signed': forall a b i,
    - b <= a ->
    a < b ->
    0 < Z.log2_up b ->
    Z.log2_up b < i ->
    Z.testbit a i = Z.testbit a (Z.log2_up b).
Proof.
  intros.
  pose proof (Z.log2_log2_up_spec b).
  apply testbit_above_signed; omega.
Qed.      

Lemma mod0_testbit: forall a i p,
    a mod 2 ^ p = 0 ->
    0 <= i < p ->
    Z.testbit a i = false.
Proof.
  intros.
  rewrite Z.testbit_false by omega.
  pose proof (Zdiv.Zmod_divides a (2 ^ p)) as P.
  destruct P as [P _].
  - apply Z.pow_nonzero; omega.
  - specialize (P H). destruct P as [c P]. subst a. clear H.
    rewrite Z.mul_comm.
    rewrite Z.divide_div_mul_exact.
    + replace p with ((1 + (p - i - 1)) + i) by omega.
      rewrite Z.pow_add_r by omega.
      rewrite Z.div_mul by (apply Z.pow_nonzero; omega).
      rewrite Zdiv.Zmult_mod.
      rewrite Z.pow_add_r by omega.
      rewrite (Zdiv.Zmult_mod (2 ^ 1)).
      change (2 ^ 1 mod 2) with 0.
      rewrite Z.mul_0_l.
      change (0 mod 2) with 0.
      rewrite Z.mul_0_r.
      reflexivity.
    + apply Z.pow_nonzero; omega.
    + replace p with ((p - i) + i) by omega.
      rewrite Z.pow_add_r by omega.
      apply Z.divide_factor_r.
Qed.
  
Lemma mod0_testbit': forall a i m,
    a mod m = 0 ->
    m = 2 ^ Z.log2_up m ->
    0 <= i < Z.log2_up m ->
    Z.testbit a i = false.
Proof.
  intros. rewrite H0 in H.
  apply (mod0_testbit a i (Z.log2_up m)); assumption.
Qed.

Lemma mod20_testbit': forall a i,
    a mod 2 = 0 ->
    i = 0 ->
    Z.testbit a i = false.
Proof.
  intros. eapply mod0_testbit'.
  - eassumption.
  - reflexivity.
  - subst. cbv. intuition congruence.
Qed.

Hint Rewrite
    Z.lxor_spec
    Z.ldiff_spec
    Z.testbit_neg_r
    Z.setbit_eq
    Z.setbit_neq
    Z.testbit_0_l
    Z.land_spec
    Z.lor_spec
    Z.shiftr_spec
    Z.lnot_spec
    Z.shiftl_spec
    testbit_minus1
    Z.ones_spec_high
    Z.ones_spec_low
    testbit_if
    using omega
: rew_testbit.

Hint Rewrite
     testbit_above'
     testbit_above_signed'
     mod0_testbit'
     mod20_testbit'
     using (try eassumption; try reflexivity; rewrite? Z.log2_up_pow2 by omega; omega)
: rew_testbit_expensive.

Ltac rewrite_testbit :=
  repeat
    ((autorewrite with bool_rewriting) ||
     (rewrite_strat (repeat (topdown (hints rew_testbit)))) ||
     ((rewrite_strat (repeat (topdown (hints rew_testbit_expensive)))))).

Ltac solve_or_split_step :=
    rewrite_testbit;
    try solve [f_equal; (reflexivity || omega)];
    match goal with
    | |- context [Z.testbit _ ?i] =>
      tryif (first [assert (0 <= i) by omega | assert (i < 0) by omega])
      then fail
      else (let C := fresh "C" in
            assert (i < 0 \/ 0 <= i) as C by omega;
            safe_ring_simplify i in C;
            destruct C as [C | C])
    end.

Ltac solve_or_split := repeat solve_or_split_step.

Ltac prove_Zeq_bitwise_pre :=
    (intuition idtac);
    subst;
    repeat (discard_contradictory_or ltac:(first [discriminate | omega ]));
    repeat (rewrite signExtend_alt2; [|omega|]);
    unfold bitSlice, signExtend2 in *;
    apply Z.bits_inj;
    unfold Z.eqf;
    intro i.

Ltac prove_Zeq_bitwise := prove_Zeq_bitwise_pre; solve_or_split.
