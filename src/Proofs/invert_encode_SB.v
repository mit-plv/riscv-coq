Require Import Coq.ZArith.BinInt.
Require Import riscv.Utility.Encode.
Require Import riscv.Utility.ZBitOps.
Require Import riscv.Utility.prove_Zeq_bitwise.

Lemma invert_encode_SB: forall {opcode rs1 rs2 funct3 sbimm12},
  verify_SB opcode rs1 rs2 funct3 sbimm12 ->
  forall inst,
  encode_SB opcode rs1 rs2 funct3 sbimm12 = inst ->
  opcode = bitSlice inst 0 7 /\
  funct3 = bitSlice inst 12 15 /\
  rs1 = bitSlice inst 15 20 /\
  rs2 = bitSlice inst 20 25 /\
  sbimm12 = signExtend 13 (Z.shiftl (bitSlice inst 31 32) 12 <|>
                           Z.shiftl (bitSlice inst 25 31) 5 <|>
                           Z.shiftl (bitSlice inst 8 12) 1  <|>
                           Z.shiftl (bitSlice inst 7 8) 11).
Proof.
  intros. unfold encode_SB, verify_SB in *.

Require Import Omega Lia.
Require Import coqutil.Z.bitblast.
Open Scope Z_scope.
Set Nested Proofs Allowed.
Close Scope z_bitwise_scope.

Lemma testbit_if: forall (b: bool) n m i,
    Z.testbit (if b then n else m) i = if b then (Z.testbit n i) else (Z.testbit m i).
Proof.
  intros. destruct b; reflexivity.
Qed.


Lemma unsigned_range_to_mask: forall {v p: Z},
    0 <= v < 2 ^ p ->
    v = Z.land v (Z.ones p).
Proof.
  intros v p [L U].
  assert (p < 0 \/ p = 0 \/ 0 < p) as C by lia; destruct C as [C | [C | C]].
  - rewrite Z.pow_neg_r in U by assumption. exfalso. lia.
  - subst p. simpl in *. replace v with 0 in * by lia. reflexivity.
  - symmetry. apply Z.land_ones_low; [assumption|].
    assert (v = 0 \/ 0 < v) as D by lia. destruct D as [D | D].
    + subst v. simpl. assumption.
    + apply Z.log2_lt_pow2; assumption.
Qed.

Lemma signed_range_to_mask: forall {v p: Z},
    - 2 ^ p <= v < 2 ^ p ->
    v = Z.land v (Z.ones p) \/
    v = Z.lor (Z.land v (Z.ones p)) (Z.shiftl (-1) p).
Proof.
  intros v p [L U].
  assert (p < 0 \/ p = 0 \/ 0 < p) as C by lia; destruct C as [C | [C | C]].
  - rewrite Z.pow_neg_r in * by assumption. exfalso. lia.
  - subst p. simpl in *.
    assert (v = -1 \/ v = 0) as D by lia. destruct D as [D | D]; subst v; simpl; auto.
  - assert (v = - 2 ^ p \/ 0 < - v < 2 ^ p \/ 0 <= v < 2 ^ p) as D by lia.
    destruct D as [D | [D | D]].
    + right. subst v. Z.bitblast.
    + right.
      Z.bitblast.
      simpl.
      rewrite Bool.orb_true_r.
      apply Z.bits_iff_neg; [|lia].
      rewrite Z.abs_neq by lia.
      apply Z.log2_lt_pow2; try lia.
      assert (2 ^ p <= 2 ^ i); try lia.
      apply Z.pow_le_mono_r; lia.
    + left. apply unsigned_range_to_mask; auto.
Qed.

Lemma signed_range_with_mod_to_mask: forall {v p q: Z},
    - 2 ^ p <= v < 2 ^ p ->
    v mod 2 ^ q = 0 ->
    0 <= q < p ->
    v = Z.land v (Z.lxor (Z.ones p) (Z.ones q)) \/
    v = Z.lor (Z.land v (Z.lxor (Z.ones p) (Z.ones q))) (Z.shiftl (-1) p).
Proof.
  intros.
  assert (2 ^ q <> 0) as A. { apply Z.pow_nonzero; lia. }
  pose proof (Z.div_mod v (2 ^ q) A) as P. rewrite H0 in P.
  rewrite Z.add_0_r in P. rewrite Z.mul_comm in P.
  rewrite <-Z.shiftl_mul_pow2 in P by lia.
  rewrite <-Z.shiftr_div_pow2 in P by lia.

  assert (0 < 2 ^ q) as B. { apply Z.pow_pos_nonneg; lia. }
  assert (2 ^ p mod 2 ^ q = 0) as C. {
    apply Znumtheory.Zdivide_mod. unfold Z.divide.
    exists (2 ^ (p - q)).
    rewrite <- Z.pow_add_r by lia.
    rewrite Z.sub_add. reflexivity.
  }

  pose proof (@signed_range_to_mask (Z.shiftr v q) (p - q)) as Q.
  destruct Q as [Q | Q].
  - rewrite Z.shiftr_div_pow2 by lia.
    rewrite Z.pow_sub_r by lia.
    split.
    + rewrite <- Z.div_opp_l_z; try lia.
      apply Z.div_le_mono; lia.
    + apply Z.div_lt_upper_bound; try lia.
      rewrite <- Zdiv.Z_div_exact_2; lia.
  - left.  rewrite P at 1. rewrite Q. Z.bitblast.
  - right. rewrite P at 1. rewrite Q. Z.bitblast.
Qed.

Ltac simpl_concrete_Zs :=
  repeat match goal with
         | |- context [?op ?a ?b] =>
           match isZcst a with true => idtac end;
           match isZcst b with true => idtac end;
           match op with
           | Z.add => idtac
           | Z.sub => idtac
           | Z.ltb => idtac
           | Z.eqb => idtac
           end;
           let r := eval cbv in (op a b) in change (op a b) with r
         end.


repeat match goal with
       | H: _ /\ _ |- _ =>
         match type of H with
         | _ <= _ < _ => fail 1
         | _ => destruct H
         end
       end.

repeat match goal with
       | H: 0 <= _ < 2 ^ _ |- _ => rewrite (unsigned_range_to_mask H); clear H
       end.

repeat match goal with
       | H1: - 2 ^ ?p <= ?x < 2 ^ ?p, H2: ?x mod _ = 0 |- _ =>
         try (change 2 with (2 ^ 1) in H2);
         let E := fresh in
         destruct (signed_range_with_mod_to_mask H1 H2) as [E | E];
           [lia | clear H1 H2; rewrite E in *; clear E ..]
       end.

{

subst.

repeat match goal with |- _ /\ _ => split end.


  Ltac discover_equal_testbit_indices :=
    repeat match goal with
           | |- context [Z.testbit _ ?i] =>
             assert_fails (is_var i);
             match isZcst i with false => idtac end;
             let l := fresh "l" in remember i as l
           end;
    repeat match goal with
           | i: Z, j: Z |- _ => replace i with j in * by lia; clear i
           end.


    5: {

    repeat (discard_contradictory_or ltac:(first [discriminate | lia ])).
    repeat (rewrite signExtend_alt2; [|omega|]);
    unfold bitSlice, signExtend2 in *.
    {
      eapply Z.bits_inj'; intros ?i ?Hi.

Hint Rewrite testbit_if: z_bitwise_no_hyps.


repeat (rewrite_strat ((repeat (topdown (choice (hints z_bitwise_no_hyps)
                                                (hints z_bitwise_with_hyps))));
                       (try (topdown (hints z_bitwise_forced_no_hyps))))).

      simpl_concrete_Zs.

(* both too slow:
      repeat match goal with
             | |- context [?a <? ?b] => progress ring_simplify a b
             end.

      discover_equal_testbit_indices.
*)



Proof. intros. unfold encode_SB, verify_SB in *. prove_Zeq_bitwise. Qed.
