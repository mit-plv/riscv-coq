Require Import Coq.ZArith.BinInt.
Require Import Coq.omega.Omega.
Require Import riscv.util.div_mod_to_quot_rem.
Require Import Coq.micromega.Lia.

Local Open Scope Z_scope.


Definition bitSlice(x: Z)(start eend: Z): Z :=
  Z.land (Z.shiftr x start) (Z.lnot (Z.shiftl (-1) (eend - start))).

Definition signExtend(l: Z)(n: Z): Z :=
  if Z.testbit n (l-1) then (n - (Z.setbit 0 l)) else n.

Definition bitSlice'(w start eend: Z): Z :=
  (w / 2 ^ start) mod (2 ^ (eend - start)).

Lemma bitSlice_alt: forall w start eend,
    0 <= start <= eend ->
    bitSlice w start eend = bitSlice' w start eend.
Proof.
  intros. unfold bitSlice, bitSlice'.
  rewrite <- Z.land_ones by omega.
  rewrite <- Z.shiftr_div_pow2 by omega.
  f_equal.
  rewrite Z.shiftl_mul_pow2 by omega.
  rewrite Z.mul_comm.
  rewrite <- Z.opp_eq_mul_m1.
  replace (Z.lnot (- 2 ^ (eend - start))) with (2 ^ (eend - start) - 1).
  - rewrite Z.ones_equiv. reflexivity.
  - pose proof (Z.add_lnot_diag (- 2 ^ (eend - start))). omega.
Qed.

Lemma bitSlice_range: forall sz z,
    0 <= sz ->
    0 <= bitSlice z 0 sz < 2 ^ sz.
Proof.
  intros.
  rewrite bitSlice_alt by omega.
  unfold bitSlice'.
  change (2 ^ 0) with 1.
  rewrite Z.div_1_r.
  rewrite Z.sub_0_r.
  apply Z.mod_pos_bound.
  apply Z.pow_pos_nonneg; omega.
Qed.

Definition signExtend'(l n: Z): Z := n - ((n / 2 ^ (l - 1)) mod 2) * 2 ^ l.

Lemma signExtend_alt: forall l n,
    0 < l ->
    signExtend l n = signExtend' l n.
Proof.
  intros. unfold signExtend, signExtend'.
  destruct (Z.testbit n (l - 1)) eqn: E.
  - apply (f_equal Z.b2z) in E.
    rewrite Z.testbit_spec' in E by omega.
    rewrite E.
    rewrite Z.setbit_spec'.
    rewrite Z.lor_0_l.
    change (Z.b2z true) with 1.
    rewrite Z.mul_1_l.
    reflexivity.
  - apply (f_equal Z.b2z) in E.
    rewrite Z.testbit_spec' in E by omega.
    rewrite E.
    change (Z.b2z false) with 0.
    rewrite Z.mul_0_l.
    rewrite Z.sub_0_r.
    reflexivity.
Qed.

Lemma mul_div2_undo_mod: forall a, 2 * (a / 2) = a - a mod 2.
Proof.
  intros.
  pose proof (Z.div_mod a 2).
  omega.
Qed.

Lemma or_to_plus: forall a b,
    Z.land a b = 0 ->
    Z.lor a b = a + b.
Proof.
  intros.
  rewrite <- Z.lxor_lor by assumption.
  symmetry. apply Z.add_nocarry_lxor. assumption.
Qed.  

Definition signExtend_alt': forall l n,
    0 < l ->
    (exists q, n / 2 ^ (l - 1) = 2 * q /\ signExtend l n = n) \/
    (exists q, n / 2 ^ (l - 1) = 2 * q + 1 /\ signExtend l n = n - 2 ^ l).
Proof.
  intros. rewrite signExtend_alt by assumption. unfold signExtend'.
  pose proof (Z.mod_pos_bound (n / 2 ^ (l - 1)) 2).
  assert ((n / 2 ^ (l - 1)) mod 2 = 0 \/ (n / 2 ^ (l - 1)) mod 2 = 1) as C by omega.
  destruct C as [C | C]; rewrite C.
  - left. exists (n / 2 ^ (l - 1) / 2). rewrite mul_div2_undo_mod. omega.
  - right. exists (n / 2 ^ (l - 1) / 2). rewrite mul_div2_undo_mod. omega.
Qed.

Definition signExtend2(l n: Z): Z :=
  if Z.testbit n (l - 1) then Z.lor n (Z.shiftl (-1) l) else n.

Lemma signExtend_alt2: forall l n,
    0 < l ->
    Z.land (Z.shiftl (-1) l) n = 0 ->
    signExtend l n = signExtend2 l n.
Proof.
  intros.
  unfold signExtend, signExtend2.
  destruct (Z.testbit n (l - 1)) eqn: E; [|reflexivity].
  rewrite <- Z.add_opp_r.
  pose proof (Z.add_lnot_diag (Z.setbit 0 l)).
  replace (- (Z.setbit 0 l)) with (Z.lnot (Z.setbit 0 l) + 1) by omega.
  replace (Z.lnot (Z.setbit 0 l) + 1) with (Z.shiftl (-1) l).
  - symmetry. apply or_to_plus. rewrite Z.land_comm. assumption.
  - replace (Z.lnot (Z.setbit 0 l)) with (- Z.setbit 0 l - 1) by omega.
    rewrite Z.shiftl_mul_pow2 by omega.
    rewrite Z.setbit_spec'.
    rewrite Z.lor_0_l.
    omega.
Qed.

Lemma bitSlice_all_nonneg: forall n v : Z,
    (0 <= n)%Z ->
    (0 <= v < 2 ^ n)%Z ->
    bitSlice v 0 n = v.
Proof.
  clear. intros.
  rewrite bitSlice_alt by omega.
  unfold bitSlice'.
  change (2 ^ 0)%Z with 1%Z.
  rewrite Z.div_1_r.
  rewrite Z.sub_0_r.
  apply Z.mod_small.
  assumption.
Qed.
      
Lemma bitSlice_all_neg: forall n v : Z,
    (0 <= n)%Z ->
    (- 2 ^ n <= v < 0)%Z ->
    bitSlice v 0 n = (2 ^ n + v)%Z.
Proof.
  clear. intros.
  rewrite bitSlice_alt by omega.
  unfold bitSlice'.
  change (2 ^ 0)%Z with 1%Z.
  rewrite Z.div_1_r.
  rewrite Z.sub_0_r.
  assert (0 < 2 ^ n)%Z. {
    apply Z.pow_pos_nonneg; omega.
  }
  div_mod_to_quot_rem.
  subst v.
  rewrite Z.add_assoc.
  assert (q = -1)%Z by nia.
  subst q.
  nia.
Qed.
