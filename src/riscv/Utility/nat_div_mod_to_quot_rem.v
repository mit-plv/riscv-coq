Require Import Coq.Arith.PeanoNat.
Require Import Coq.ZArith.ZArith.
Require Import riscv.Utility.Tactics.
Require Import coqutil.Z.Lia.

Local Open Scope nat_scope.


Lemma rewrite_div_mod: forall (a b: nat),
    b <> 0 ->
    exists q r, a mod b = r /\ a / b = q /\ a = b * q + r /\ r < b.
Proof.
  intros.
  exists (a / b). exists (a mod b).
  rewrite <- (Nat.div_mod a b) by assumption.
  pose proof (Nat.mod_upper_bound a b).
  auto.
Qed.

Ltac nat_div_mod_to_quot_rem_step :=
  so fun hyporgoal => match hyporgoal with
  | context [?a mod ?b] =>
      let Ne := fresh "Ne" in
      let P := fresh "P" in
      assert (b <> 0) as Ne by blia;
      pose proof (rewrite_div_mod a b Ne) as P;
      clear Ne;
      let q := fresh "q" in
      let r := fresh "r" in
      let Er := fresh "Er" in
      let Eq := fresh "Eq" in
      let E := fresh "E" in
      let B := fresh "B" in
      destruct P as [ q [ r [ Er [ Eq [ E B ] ] ] ] ];
      rewrite? Er in *;
      rewrite? Eq in *;
      clear Er Eq
  end.

Ltac nat_div_mod_to_quot_rem := repeat nat_div_mod_to_quot_rem_step.
