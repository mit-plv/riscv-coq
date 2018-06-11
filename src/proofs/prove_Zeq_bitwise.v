Require Import Coq.ZArith.BinInt.
Require Import Coq.omega.Omega.
Require Import Coq.micromega.Lia.
Require Import riscv.util.Tactics.
Require Import riscv.util.div_mod_to_quot_rem.
Require Import riscv.util.ZBitOps.


Local Open Scope bool_scope.
Local Open Scope Z_scope.


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

Lemma then_false_else_true: forall (b: bool),
    (if b then false else true) = negb b.
Proof.
  intros. destruct b; reflexivity.
Qed.

Hint Rewrite if_same then_true_else_false then_false_else_true : bool_rewriting.

Hint Rewrite
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

Ltac simpl_pow2 :=
  repeat (so fun hyporgoal => match hyporgoal with
     | context [2 ^ ?x] => let r := eval cbv in (2 ^ x) in change (2 ^ x) with r in *
  end).

Ltac simpl_log2up :=
  repeat match goal with
         | |- context [Z.log2_up ?a] =>
           let r := eval cbv in (Z.log2_up a) in change (Z.log2_up a) with r
         end.

Lemma testbit_above': forall n b i,
    0 <= n < b ->
    0 <= Z.log2_up b ->
    Z.log2_up b <= i ->
    Z.testbit n i = false.
Proof.
  intros.
  pose proof (Z.log2_log2_up_spec b).
  apply (@testbit_above (Z.log2_up b) n); omega.
Qed.

Lemma testbit_above_signed': forall a b i,
    - b <= a < b ->
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

Ltac rewrite_testbit :=
    repeat ((autorewrite with bool_rewriting) ||
            (match goal with
             | |- context [ Z.testbit _ ?i ] =>
                     (rewrite Z.lxor_spec) ||
                     (rewrite Z.ldiff_spec) ||
                     (rewrite (Z.testbit_neg_r _ i) by omega) ||
                     (rewrite (Z.setbit_eq _ i) by omega) ||
                     (rewrite (Z.setbit_neq _ _ i) by omega) ||
                     (rewrite Z.testbit_0_l) ||
                     (rewrite Z.land_spec) ||
                     (rewrite Z.lor_spec) ||
                     (rewrite (Z.shiftr_spec _ _ i) by omega) ||
                     (rewrite (Z.lnot_spec _ i) by omega) ||
                     (rewrite (Z.shiftl_spec _ _ i) by omega) ||
                     (rewrite (Z.testbit_neg_r _ i) by omega) ||
                     (rewrite testbit_minus1 by omega) ||
                     (rewrite (Z.ones_spec_high _ i) by omega) ||
                     (rewrite (Z.ones_spec_low _ i) by omega) ||
                     (rewrite testbit_if) ||
                     (match goal with
                      | H1: 0 <= ?a, H2: ?a < ?b |- _ =>
                          rewrite (testbit_above' a b) by (simpl_log2up; omega)
                      | H1: - ?b <= ?a, H2: ?a < ?b |- _ =>
                          rewrite (testbit_above_signed' a b) by (simpl_log2up; omega);
                          simpl_log2up
                      | H1: ?a mod ?m = 0 |- _ =>
                          rewrite (mod0_testbit' a i m) by (simpl_log2up; simpl_pow2; omega)
                      end)
             end)).

Ltac prove_Zeq_bitwise :=
    (intuition idtac);
    subst;
    simpl_pow2;
    repeat (discard_contradictory_or omega);
    repeat (rewrite signExtend_alt2; [|omega|]);
    unfold bitSlice, signExtend2 in *;
    apply Z.bits_inj;
    unfold Z.eqf;
    intro i;
    repeat (rewrite_testbit;
            try solve [f_equal; (reflexivity || omega)];
            match goal with
            | |- context [Z.testbit _ ?i] =>
              tryif (first [assert (0 <= i) by omega | assert (i < 0) by omega])
              then fail
              else (let C := fresh "C" in
                    assert (i < 0 \/ 0 <= i) as C by omega;
                    destruct C as [C | C])
            end).
