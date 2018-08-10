Require Import Coq.ZArith.ZArith.
Require Import bbv.WordScope.


Definition riscv_signed_div{sz: nat}(a b: word (S sz)): word (S sz) :=
  if weqb b $0 then wones (S sz) else
    if andb (weqb a (wpow2 sz)) (weqb b (wones (S sz))) then wpow2 sz else
      wordBinZ Z.quot a b.

Definition riscv_signed_rem{sz: nat}(a b: word (S sz)): word (S sz) :=
  if weqb b $0 then a else
    if andb (weqb a (wpow2 sz)) (weqb b (wones (S sz))) then $0 else
      wordBinZ Z.rem a b.

Definition riscv_unsigned_div{sz: nat}(a b: word sz): word sz :=
  if weqb b $0 then wones sz else wdiv a b.

Definition riscv_unsigned_rem{sz: nat}(a b: word sz): word sz :=
  if weqb b $0 then a else wmod a b.


Lemma riscv_signed_div_def: forall sz (a b : word (S sz)),
    b <> ZToWord (S sz) 0 ->
    ~ (a = wpow2 sz /\ b = wones (S sz)) ->
    riscv_signed_div a b = ZToWord (S sz) (Z.quot (wordToZ a) (wordToZ b)).
Proof.
  intros.
  unfold riscv_signed_div.
  rewrite ZToWord_0 in H.
  rewrite weqb_ne by assumption.
  match goal with
  | |- (if ?b then _ else _) = _ => destruct b eqn: E; [|reflexivity]
  end.
  exfalso.
  apply Bool.andb_true_iff in E. destruct E as [E1 E2].
  apply weqb_sound in E1.
  apply weqb_sound in E2.
  subst.
  apply H0. split; reflexivity.
Qed.

Lemma riscv_signed_rem_def: forall sz (a b : word (S sz)),
    b <> ZToWord (S sz) 0 ->
    ~ (a = wpow2 sz /\ b = wones (S sz)) ->
    riscv_signed_rem a b = ZToWord (S sz) (Z.rem (wordToZ a) (wordToZ b)).
Proof.
  intros.
  unfold riscv_signed_rem.
  rewrite ZToWord_0 in H.
  rewrite weqb_ne by assumption.
  match goal with
  | |- (if ?b then _ else _) = _ => destruct b eqn: E; [|reflexivity]
  end.
  exfalso.
  apply Bool.andb_true_iff in E. destruct E as [E1 E2].
  apply weqb_sound in E1.
  apply weqb_sound in E2.
  subst.
  apply H0. split; reflexivity.
Qed.

Lemma riscv_unsigned_div_def: forall sz (a b : word sz),
    b <> ZToWord sz 0 ->
    riscv_unsigned_div a b = ZToWord sz (Z.quot (uwordToZ a) (uwordToZ b)).
Proof.
  intros.
  unfold riscv_unsigned_div.
  rewrite ZToWord_0 in H.
  rewrite weqb_ne by assumption.
  unfold wdiv, wordBin, uwordToZ.
  rewrite <- N2Z.inj_quot.
  rewrite ZToWord_Z_of_N.
  reflexivity.
Qed.

Lemma riscv_unsigned_rem_def: forall sz (a b : word sz),
    b <> ZToWord sz 0 ->
    riscv_unsigned_rem a b = ZToWord sz (Z.rem (uwordToZ a) (uwordToZ b)).
Proof.
  intros.
  unfold riscv_unsigned_rem.
  rewrite ZToWord_0 in H.
  rewrite weqb_ne by assumption.
  unfold wmod, wordBin, uwordToZ.
  rewrite <- N2Z.inj_rem.
  rewrite ZToWord_Z_of_N.
  reflexivity.
Qed.
