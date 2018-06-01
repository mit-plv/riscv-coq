Require Import Coq.ZArith.BinInt.
Require Import bbv.Word.
Require Import riscv.Decode.
Require Import riscv.encode.Encode.
Require Import riscv.Utility.
Require Import Coq.omega.Omega.

Local Open Scope bool_scope.
Local Open Scope Z_scope.

Lemma mul_div2_undo_mod: forall a, 2 * (a / 2) = a - a mod 2.
Proof.
  intros.
  pose proof (Z.div_mod a 2).
  omega.
Qed.

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

Definition signExtend'(l n: Z): Z := n - ((n / 2 ^ (l - 1)) mod 2) * 2 ^ l.

Definition signExtend_alt: forall l n,
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

Lemma or_to_plus: forall a b,
    Z.land a b = 0 ->
    a <|> b = a + b.
Proof.
  intros.
  rewrite <- Z.lxor_lor by assumption.
  symmetry. apply Z.add_nocarry_lxor. assumption.
Qed.  

Tactic Notation "so" tactic(f) :=
  match goal with
  | _: ?A |- _  => f A
  |       |- ?A => f A
  end.

Module ThanksFiatCrypto.
  Ltac div_mod_to_quot_rem_inequality_solver := omega.

  Ltac generalize_div_eucl x y :=
    let H := fresh in
    let H' := fresh in
    assert (H' : y <> 0) by div_mod_to_quot_rem_inequality_solver;
    generalize (Z.div_mod x y H'); clear H';
    first [ assert (H' : 0 < y) by div_mod_to_quot_rem_inequality_solver;
            generalize (Z.mod_pos_bound x y H'); clear H'
          | assert (H' : y < 0) by div_mod_to_quot_rem_inequality_solver;
            generalize (Z.mod_neg_bound x y H'); clear H'
          | assert (H' : y < 0 \/ 0 < y) by (apply Z.neg_pos_cases; div_mod_to_quot_rem_inequality_solver);
            let H'' := fresh in
            assert (H'' : y < x mod y <= 0 \/ 0 <= x mod y < y)
              by (destruct H'; [ left; apply Z.mod_neg_bound; assumption
                               | right; apply Z.mod_pos_bound; assumption ]);
            clear H'; revert H'' ];
    let q := fresh "q" in
    let r := fresh "r" in
    set (q := x / y) in *;
    set (r := x mod y) in *;
    clearbody q r.

  Ltac div_mod_to_quot_rem_step :=
    so fun hyporgoal => match hyporgoal with
    | context[?x / ?y] => generalize_div_eucl x y
    | context[?x mod ?y] => generalize_div_eucl x y
    end.

  Ltac div_mod_to_quot_rem := repeat div_mod_to_quot_rem_step; intros.

End ThanksFiatCrypto.

Ltac somega_pre :=
  rewrite? bitSlice_alt in * by omega; unfold bitSlice' in *;
  repeat (so fun hyporgoal => match hyporgoal with
  | context [signExtend ?l ?n] =>
      let E := fresh "E" in
      destruct (signExtend_alt' l n) as [[? [? E]] | [? [? E]]];
      [ omega | rewrite E in *; clear E .. ]
  end);
  rewrite? Z.shiftl_mul_pow2 in * by omega;
  repeat (so fun hyporgoal => match hyporgoal with
     | context [2 ^ ?x] => let r := eval cbv in (2 ^ x) in change (2 ^ x) with r in *
  end);
  ThanksFiatCrypto.div_mod_to_quot_rem;
  repeat match goal with
         | z: ?T |- _ => progress change T with Z in *
         end.

(* omega which understands bitSlice and shift *)
Ltac somega := somega_pre; omega.

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

Ltac write_as_pow2_opportunities f :=
    repeat (so fun hyporgoal => match hyporgoal with
               | context [ Z.pos ?p ] =>
                   match p with
                   | 1%positive => fail 1
                   | 2%positive => fail 1
                   | _ => idtac
                   end;
                   let e := eval cbv in (Z.log2 (Z.pos p)) in
                   f (Z.pos p) (2 ^ e)
               end);
    (* we might have been a bit too eager -- undo undesired chained powers: *)
    repeat (so fun hyporgoal => match hyporgoal with
               | context [2 ^ 2 ^ ?p] => let r := eval cbv in (2 ^ p) in
                                         change (2 ^ 2 ^ p) with (2 ^ r) in *
               end).

Tactic Notation "write_as_pow2" "in" "*|-" :=
  write_as_pow2_opportunities ltac:(fun old new => change old with new in *|-).

Tactic Notation "write_as_pow2" "in" "*" :=
  write_as_pow2_opportunities ltac:(fun old new => change old with new in *).

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

Lemma signExtend_cases: forall a n l,
    0 < l ->
    - 2 ^ (l - 1) <= a < 2 ^ (l - 1) ->
    (0 <= a -> a = n) ->
    (a < 0 -> a = Z.lxor n (Z.shiftl (-1) l)) ->
    a = signExtend l n.
Proof.
  intros.
  unfold signExtend.
  assert (0 <= a \/ a < 0) as C by omega.
  destruct C as [C | C].
  - specialize (H1 C). clear H2. subst a.
    destruct (Z.testbit n (l - 1)) eqn: E.
    + exfalso.
      apply Z.testbit_true in E; [|omega].
      rewrite Z.div_small in E by omega.
      cbv in E. discriminate.
    + reflexivity.
  - specialize (H2 C). clear H1.
    destruct (Z.testbit n (l - 1)) eqn: E.
    + subst a. exfalso.
      assert (n < 0 \/ 0 <= n < 2 ^ (l - 1) \/ 2 ^ (l - 1) <= n) as D by omega.
      destruct D as [D | [D | D]].
      * rewrite Z.shiftl_mul_pow2 in C by omega.
        (* xor of two negative numbers is positive, contradicts C *)
        admit.
      * apply Z.testbit_true in E; [|omega].
        rewrite Z.div_small in E by omega.
        cbv in E. discriminate.
      * (* n has some bits past l-1 set, xor with (Z.shiftl (-1) l) will result in a too
           negative number, contradicting H0. *)
        admit.
    + subst a.
      assert (n < 0 \/ 0 <= n < 2 ^ (l - 1) \/ 2 ^ (l - 1) <= n) as D by omega.
      destruct D as [D | [D | D]].
      * rewrite Z.shiftl_mul_pow2 in C by omega.
        (* xor of two negative numbers is positive, contradicts C *)
        admit.
      * (* This case does not hold:
           n small positive, a negative *)
Abort.        

Ltac discard_contradictory_or t :=
  match goal with
  | |- ?P \/ ?Q => (assert (~P) as _ by t; right) || (assert (~Q) as _ by t; left)
  end.

Ltac prove_Zeq_bitwise :=
    intuition idtac;
    subst;
    write_as_pow2 in *|-;
    repeat (discard_contradictory_or omega);
    apply Z.bits_inj;
    unfold Z.eqf;
    intro i;
    match goal with
    | _: 0 <= ?f, _: ?f < 2 ^ ?p |- Z.testbit ?f ?i = _ =>
        let C := fresh "C" in
        assert (i < 0 \/ 0 <= i < p \/ p = i \/ p < i) as C by omega;
        destruct C as [C | [C | [C | C]]]
    | |- Z.testbit (bitSlice _ ?start ?eend) ?i = _ =>
        let C := fresh "C" in
        assert (i < 0 \/ i = 0 \/  0 < i < start \/ start <= i < eend \/ eend <= i) as C by omega;
        destruct C as [C | [C | [C | [C | C]]]]
    end;
    unfold bitSlice in *;
    repeat match goal with
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
                     (match goal with
                      | H: 0 <= _ < 2 ^ _ |- _ =>
                          rewrite (testbit_above H) by omega
                      | H1: 0 <= ?a, H2: ?a < 2 ^ _ |- _ =>
                          rewrite (testbit_above (conj H1 H2)) by omega
                      end)
           end;
    autorewrite with bool_rewriting;
    f_equal;
    try reflexivity;
    try omega.

Lemma invert_encode_InvalidInstruction: forall i,
  verify_Invalid i ->
  forall inst,
  encode_Invalid i = inst ->
  False.
Proof. intros. assumption. Qed.

Lemma invert_encode_R: forall {opcode rd rs1 rs2 funct3 funct7},
  verify_R opcode rd rs1 rs2 funct3 funct7 ->
  forall inst,
  encode_R opcode rd rs1 rs2 funct3 funct7 = inst ->
  opcode = bitSlice inst 0 7 /\
  funct3 = bitSlice inst 12 15 /\
  funct7 = bitSlice inst 25 32 /\
  rd = bitSlice inst 7 12 /\
  rs1 = bitSlice inst 15 20 /\
  rs2 = bitSlice inst 20 25.
Proof. intros. unfold encode_R, verify_R in *. prove_Zeq_bitwise. Qed.

Lemma invert_encode_R_atomic: forall {opcode rd rs1 rs2 funct3 aqrl funct5},
  verify_R_atomic opcode rd rs1 rs2 funct3 aqrl funct5 ->
  forall inst,
  encode_R_atomic opcode rd rs1 rs2 funct3 aqrl funct5 = inst ->
  opcode = bitSlice inst 0 7 /\
  funct3 = bitSlice inst 12 15 /\
  aqrl = bitSlice inst 25 27 /\
  funct5 = bitSlice inst 27 32 /\
  rd = bitSlice inst 7 12 /\
  rs1 = bitSlice inst 15 20 /\
  rs2 = bitSlice inst 20 25.
Proof. intros. unfold encode_R_atomic, verify_R_atomic in *. prove_Zeq_bitwise. Qed.

Lemma invert_encode_I: forall {opcode rd rs1 funct3 oimm12},
  verify_I opcode rd rs1 funct3 oimm12 ->
  forall inst,
  encode_I opcode rd rs1 funct3 oimm12 = inst ->
  opcode = bitSlice inst 0 7 /\
  funct3 = bitSlice inst 12 15 /\
  rd = bitSlice inst 7 12 /\
  rs1 = bitSlice inst 15 20 /\
  oimm12 = signExtend 12 (bitSlice inst 20 32).
Proof. intros. unfold encode_I, verify_I in *. Fail prove_Zeq_bitwise. Admitted.

Lemma invert_encode_I_shift_57: forall {opcode rd rs1 shamt5 funct3 funct7},
  verify_I_shift_57 opcode rd rs1 shamt5 funct3 funct7 ->
  forall inst,
  encode_I_shift_57 opcode rd rs1 shamt5 funct3 funct7 = inst ->
  opcode = bitSlice inst 0 7 /\
  funct3 = bitSlice inst 12 15 /\
  funct7 = bitSlice inst 25 32 /\
  rd = bitSlice inst 7 12 /\
  rs1 = bitSlice inst 15 20 /\
  shamt5 = bitSlice inst 20 25.
Proof. intros. unfold encode_I_shift_57, verify_I_shift_57 in *. prove_Zeq_bitwise. Qed.

Lemma invert_encode_I_shift_66: forall {bitwidth opcode rd rs1 shamt6 funct3 funct6},
  verify_I_shift_66 bitwidth opcode rd rs1 shamt6 funct3 funct6 ->
  forall inst,
  encode_I_shift_66  opcode rd rs1 shamt6 funct3 funct6 = inst ->
  opcode = bitSlice inst 0 7 /\
  funct3 = bitSlice inst 12 15 /\
  funct6 = bitSlice inst 26 32 /\
  rd = bitSlice inst 7 12 /\
  rs1 = bitSlice inst 15 20 /\
  shamt6 = bitSlice inst 20 26 /\
  ((Z.eqb (bitSlice inst 25 26) 0) || (Z.eqb bitwidth 64)) = true.
Proof.
  intros. unfold encode_I_shift_66, verify_I_shift_66 in *.
  rewrite Bool.orb_true_iff.
  rewrite? Z.eqb_eq.
  prove_Zeq_bitwise.
Qed.

Lemma invert_encode_I_system: forall {opcode rd rs1 funct3 funct12},
  verify_I_system opcode rd rs1 funct3 funct12 ->
  forall inst,
  encode_I_system opcode rd rs1 funct3 funct12 = inst ->
  opcode = bitSlice inst 0 7 /\
  funct3 = bitSlice inst 12 15 /\
  funct12 = bitSlice inst 20 32 /\
  rd = bitSlice inst 7 12 /\
  rs1 = bitSlice inst 15 20.
Proof. intros. unfold encode_I_system, verify_I_system in *. prove_Zeq_bitwise. Qed.

Lemma testbit_if: forall (b: bool) n m i,
    Z.testbit (if b then n else m) i = if b then (Z.testbit n i) else (Z.testbit m i).
Proof.
  intros. destruct b; reflexivity.
Qed.

Definition signExtend'''(l n: Z): Z :=
  if Z.testbit n (l - 1) then Z.lxor n (Z.shiftl (-1) l) else n.

Definition signExtend''(l n: Z): Z :=
  if Z.testbit n (l - 1) then Z.ldiff n (Z.setbit 0 l) else n.

Lemma signExtend_alt'': forall l n,
    signExtend l n = signExtend'' l n.
Proof.
  intros. unfold signExtend, signExtend''.
  destruct (Z.testbit n (l - 1)) eqn: E; [|reflexivity].
  destruct (Z.testbit n l) eqn: F.
  - apply Z.sub_nocarry_ldiff. admit. (* ok *)
  - (* rhs in n, lhs is not n -> does not hold! *)
Abort.

Definition signExtend1(l n: Z): Z :=
  if Z.testbit n (l - 1) then
    if Z.testbit n l then
      Z.ldiff n (Z.setbit 0 l)
    else
      333
  else n.

Lemma signExtend_alt1: forall l n,
    signExtend l n = signExtend1 l n.
Proof.
  intros. unfold signExtend, signExtend1.
  destruct (Z.testbit n (l - 1)) eqn: E; [|reflexivity].
  destruct (Z.testbit n l) eqn: F.
  - apply Z.sub_nocarry_ldiff. admit. (* ok *)
  - (* rhs in n, lhs is not n -> does not hold! *)
Abort.

Definition fakemask(a l: Z): Z :=
    Z.land (Z.shiftl (-1) l) a <|> Z.land (Z.ones l) a.

Lemma fakemask_id: forall a l,
    0 < l ->
    fakemask a l = a.
Proof.
  intros. unfold fakemask.
  pose proof (Z.lnot_lor 0 (Z.lnot a)) as P.
  rewrite Z.lor_0_l in P.
  rewrite Z.lnot_involutive in P.
  rewrite P at 3.
  replace (Z.lnot 0) with (Z.lor (Z.shiftl (-1) l) (Z.ones l)).
  - symmetry. apply Z.land_lor_distr_l.
  - apply Z.bits_inj;
    unfold Z.eqf;
    intro i.
    assert (i < 0 \/ 0 <= i < l \/ i = l \/ l < i) as C by omega.
    destruct C as [C | [C | [C | C]]];    
    repeat match goal with
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
                     (match goal with
                      | H: 0 <= _ < 2 ^ _ |- _ =>
                          rewrite (testbit_above H) by omega
                      | H1: 0 <= ?a, H2: ?a < 2 ^ _ |- _ =>
                          rewrite (testbit_above (conj H1 H2)) by omega
                      end)
           end;
    autorewrite with bool_rewriting;
    f_equal;
    try reflexivity;
    try omega.
Qed.

Definition signExtend7(l n: Z): Z :=
  if Z.testbit n (l - 1) then
    Z.land (Z.shiftl (-1) l) (n - Z.setbit 0 l) <|> Z.land (Z.ones l) (Z.ldiff n (Z.setbit 0 l))
  else n.
(* not what we want: Z.land with Z.ones makes negative number positive *)

Definition signExtend2(l n: Z): Z :=
  if Z.testbit n (l - 1) then
    (Z.land (Z.shiftl (-1) l) (n - Z.setbit 0 l)) <|>
    (* ^-- only bits higher than l will be set, and we will never read these -- Not true!! *)
    (Z.land (Z.ones l) n)
    (* (n <|> (Z.shiftl (-1) l)) *)                                              
    (*    (Z.ldiff (Z.land (Z.ones l) n) (Z.setbit 0 l)) *)
  else n.

Lemma signExtend_alt2: forall l n,
    signExtend l n = signExtend2 l n.
Proof.
  intros. unfold signExtend, signExtend2.
  destruct (Z.testbit n (l - 1)) eqn: E; [|reflexivity].
  (* might hold, but probably not useful *)
Abort.

(*
Lemma signExtend_alt2: forall l n,
    signExtend l n = signExtend2 l n.
Proof.
  intros. unfold signExtend, signExtend2.
  destruct (Z.testbit n (l - 1)) eqn: E; [|reflexivity].
  rewrite Z.lor_land_distr_l.
  rewrite Z.lor_assoc.
  rewrite Z.lor_comm.
  rewrite Z.lor_assoc.
  rewrite Z.lor_diag.
  rewrite Z.lor_comm.

Abort.
*)


Lemma testbit_signExtend: forall l n i,
    exists b, Z.testbit (signExtend l n) i = b.
Proof.
  intros.
  unfold signExtend.
  destruct (Z.testbit n (l - 1)) eqn: E.
  - destruct (Z.testbit n l) eqn: F.
    + setoid_rewrite Z.sub_nocarry_ldiff.
      * exists (Z.testbit n i).
        f_equal.
        admit. (*ok*)
      * (* ok *)
        admit.
    + 
Abort.
  
Lemma invert_encode_S: forall {opcode rs1 rs2 funct3 simm12},
  verify_S opcode rs1 rs2 funct3 simm12 ->
  forall inst,
  encode_S opcode rs1 rs2 funct3 simm12 = inst ->
  opcode = bitSlice inst 0 7 /\
  funct3 = bitSlice inst 12 15 /\
  rs1 = bitSlice inst 15 20 /\
  rs2 = bitSlice inst 20 25 /\
  simm12 = signExtend 12 (Z.shiftl (bitSlice inst 25 32) 5 <|> bitSlice inst 7 12).
Proof.
  intros. unfold encode_S, verify_S in *.
  repeat split; try solve [prove_Zeq_bitwise].
  
(*
    (intuition idtac);
    subst;
    write_as_pow2 in *|-;
    repeat (discard_contradictory_or omega);
    apply Z.bits_inj;
    unfold Z.eqf;
    intro i;
    match goal with
    | _: 0 <= ?f, _: ?f < 2 ^ ?p |- Z.testbit ?f ?i = _ =>
        let C := fresh "C" in
        assert (i < 0 \/ 0 <= i < p \/ p = i \/ p < i) as C by omega;
        destruct C as [C | [C | [C | C]]]
    | _: - 2 ^ ?p <= ?f, _: ?f < 2 ^ ?p |- Z.testbit ?f ?i = _ =>
        let C := fresh "C" in
        assert (i < 0 \/ 0 <= i < p \/ p = i \/ p < i) as C by omega;
        destruct C as [C | [C | [C | C]]]
    | |- Z.testbit (bitSlice _ ?start ?eend) ?i = _ =>
        let C := fresh "C" in
        assert (i < 0 \/ i = 0 \/  0 < i < start \/ start <= i < eend \/ eend <= i) as C by omega;
        destruct C as [C | [C | [C | [C | C]]]]
    end;
    unfold bitSlice, signExtend in *;
    repeat match goal with
             | |- context [ Z.testbit _ ?i ] =>
                     (rewrite (Z.testbit_neg_r _ i) by omega) ||
                     (rewrite Z.testbit_0_l) ||
                     (rewrite Z.land_spec) ||
                     (rewrite Z.lor_spec) ||
                     (rewrite (Z.shiftr_spec _ _ i) by omega) ||
                     (rewrite (Z.lnot_spec _ i) by omega) ||
                     (rewrite (Z.shiftl_spec _ _ i) by omega) ||
                     (rewrite (Z.testbit_neg_r _ i) by omega) ||
                     (rewrite testbit_minus1 by omega) ||
                     (rewrite testbit_if) ||
                     (match goal with
                      | H: 0 <= _ < 2 ^ _ |- _ =>
                          rewrite (testbit_above H) by omega
                      | H1: 0 <= ?a, H2: ?a < 2 ^ _ |- _ =>
                          rewrite (testbit_above (conj H1 H2)) by omega
                      end)
           end;
    autorewrite with bool_rewriting;
    try solve [f_equal; (reflexivity || omega)].
*)
  (* Problem: need to get rid of subtraction because that's hard to relate to testbit *)

  
Admitted. (*
  rewrite or_to_plus.
  + somega.    
  + apply Z.bits_inj.
    unfold Z.eqf.
    intro i.
    rewrite Z.bits_0.
    rewrite Z.land_spec.
    rewrite Bool.andb_false_iff.
    assert (i < 0 \/ 0 <= i < 5 \/ 5 <= i) as C by omega. destruct C as [C | [C | C]].
    - rewrite Z.testbit_neg_r; auto.
    - rewrite Z.shiftl_spec by omega.
      rewrite Z.testbit_neg_r by omega. auto.
    - right. rewrite bitSlice_alt by omega. unfold bitSlice'.
      apply Z.mod_pow2_bits_high.
      omega.
Qed.
*)

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
  repeat split; try prove_Zeq_bitwise.
Admitted.

Lemma invert_encode_U: forall {opcode rd imm20},
  verify_U opcode rd imm20 ->
  forall inst,
  encode_U opcode rd imm20 = inst ->
  opcode = bitSlice inst 0 7 /\
  rd = bitSlice inst 7 12 /\
  imm20 = signExtend 32 (Z.shiftl (bitSlice inst 12 32) 12).
Proof.
  intros. unfold encode_U, verify_U in *.
Admitted.

Lemma invert_encode_UJ: forall {opcode rd jimm20},
  verify_UJ opcode rd jimm20 ->
  forall inst,
  encode_UJ opcode rd jimm20 = inst ->
  opcode = bitSlice inst 0 7 /\
  rd = bitSlice inst 7 12 /\
  jimm20 = signExtend 21 (Z.shiftl (bitSlice inst 31 32) 20  <|>
                          Z.shiftl (bitSlice inst 21 31) 1  <|>
                          Z.shiftl (bitSlice inst 20 21) 11 <|>
                          Z.shiftl (bitSlice inst 12 20) 12).
Proof.
  intros. unfold encode_UJ, verify_UJ in *.
Admitted.

Lemma invert_encode_Fence: forall {opcode rd rs1 funct3 prd scc msb4},
  verify_Fence opcode rd rs1 funct3 prd scc msb4 ->
  forall inst,
  encode_Fence opcode rd rs1 funct3 prd scc msb4 = inst ->
  opcode = bitSlice inst 0 7 /\
  funct3 = bitSlice inst 12 15 /\
  rd = bitSlice inst 7 12 /\
  rs1 = bitSlice inst 15 20 /\
  scc = bitSlice inst 20 24 /\
  prd = bitSlice inst 24 28 /\
  msb4 = bitSlice inst 28 32.
Proof. intros. unfold encode_Fence, verify_Fence in *. prove_Zeq_bitwise. Qed.

Ltac cbn_encode := repeat (
    cbn [
      Z.eqb Pos.eqb andb
opcode_SYSTEM
opcode_STORE_FP
opcode_STORE
opcode_OP_IMM_32
opcode_OP_IMM
opcode_OP_FP
opcode_OP_32
opcode_OP
opcode_NMSUB
opcode_NMADD
opcode_MSUB
opcode_MISC_MEM
opcode_MADD
opcode_LUI
opcode_LOAD_FP
opcode_LOAD
opcode_JALR
opcode_JAL
opcode_BRANCH
opcode_AUIPC
opcode_AMO
funct3_JALR
funct7_XOR
funct7_SUBW
funct7_SRLIW
funct7_SRL
funct7_SUB
funct7_SRLW
funct7_SRA
funct7_SLTU
funct7_SLT
funct7_SLLW
funct7_SLLIW
funct7_SLL
funct7_SRAW
funct7_SRAIW
funct7_MUL
funct7_DIVW
funct7_DIVUW
funct7_DIVU
funct7_DIV
funct7_AND
funct7_SFENCE_VMA
funct7_REMW
funct7_REMUW
funct7_REMU
funct7_REM
funct7_OR
funct7_MULW
funct7_MULHU
funct7_MULHSU
funct7_MULH
funct3_SRAIW
funct3_SRAI
funct3_SRA
funct3_SLTU
funct3_SLTIU
funct3_SLTI
funct7_ADDW
funct7_ADD
funct6_SRLI
funct6_SRAI
funct6_SLLI
funct5_SC
funct5_LR
funct5_AMOXOR
funct5_AMOSWAP
funct5_AMOOR
funct5_AMOMINU
funct5_AMOMIN
funct5_AMOMAXU
funct5_AMOMAX
funct5_AMOAND
funct5_AMOADD
funct3_XORI
funct3_XOR
funct3_SW
funct3_SUBW
funct3_SUB
funct3_SRLW
funct3_SRLIW
funct3_SRLI
funct3_SRL
funct3_SRAW
funct12_EBREAK
funct3_DIVUW
funct3_SLT
funct3_SLLW
funct3_SLLIW
funct3_SLLI
funct3_SLL
funct3_SH
funct3_SD
funct3_SB
funct3_REMW
funct3_REMUW
funct3_REMU
funct3_REM
funct3_PRIV
funct3_ORI
funct3_OR
funct3_MULW
funct3_MULHU
funct3_MULHSU
funct3_MULH
funct3_MUL
funct3_LWU
funct3_LW
funct3_LHU
funct3_LH
funct3_LD
funct3_LBU
funct3_LB
funct3_FENCE_I
funct3_FENCE
funct3_DIVW
funct3_AND
funct3_DIVU
funct3_DIV
funct3_CSRRWI
funct3_CSRRW
funct3_CSRRSI
funct3_CSRRS
funct3_CSRRCI
funct3_CSRRC
funct3_BNE
funct3_BLTU
funct3_BLT
funct3_BGEU
funct3_BGE
funct3_BEQ
funct3_ANDI
funct12_URET
funct3_AMOW
funct3_AMOD
funct3_ADDW
funct3_ADDIW
funct3_ADDI
funct3_ADD
funct12_WFI
funct12_MRET
funct12_SRET
funct12_ECALL
isValidM64
isValidM
isValidI64
isValidI
isValidCSR
isValidA64
isValidA
supportsM
supportsA
bitwidth
app
] in *;
cbv [machineIntToShamt id] in *).

Lemma decode_encode (inst: Instruction) (H:respects_bounds 64 inst) :
    decode RV64IMA (encode inst) = inst.
Proof.
  cbv beta delta [decode].
  repeat match goal with
  | |- (let x := ?a in ?b) = ?c => change (let x := a in b = c); intro
  | x := ?t : ?T |- _ => pose proof (eq_refl t : x = t); clearbody x
  end.
  remember (encode inst) as encoded eqn:Henc; symmetry in Henc.
  cbv [encode] in Henc.
  cbv [
      Encoder
        Verifier
        apply_InstructionMapper 
        map_Fence
        map_I
        map_I_shift_57
        map_I_shift_66
        map_I_system
        map_Invalid
        map_R
        map_R_atomic
        map_S
        map_SB
        map_U
        map_UJ
    ] in Henc.

  destruct inst as [i|i|i|i|i|i|i|i].
  par: abstract (destruct i; try (
    (lazymatch type of Henc with
     | encode_I _ _ _ _ _ = _ =>
       apply invert_encode_I in Henc
     | encode_Fence _ _ _ _ _ _ _ = _ =>
       apply invert_encode_Fence in Henc
     | encode_I_shift_66 _ _ _ _ _ _ = _ =>
       apply (invert_encode_I_shift_66(bitwidth:=64)) in Henc
     | encode_I_shift_57 _ _ _ _ _ _ = _ =>
       apply invert_encode_I_shift_57 in Henc
     | encode_R _ _ _ _ _ _ = _ =>
       apply invert_encode_R in Henc
     | encode_Invalid _ = _ =>
       apply invert_encode_InvalidInstruction in Henc
     | encode_R_atomic _ _ _ _ _ _ _ = _ => 
       apply invert_encode_R_atomic in Henc
     | encode_I_system _ _ _ _ _ = _ =>
       apply invert_encode_I_system in Henc
     | encode_U _ _ _ = _ =>
       apply invert_encode_U in Henc
     | encode_UJ _ _ _ = _ =>
       apply invert_encode_UJ in Henc
     | encode_S _ _ _ _ _ = _ =>
       apply invert_encode_S in Henc
     | encode_SB _ _ _ _ _ = _ => 
       apply invert_encode_SB in Henc
     end; [|trivial]);
      repeat match type of Henc with
               _ /\ _ => let H := fresh "H" in destruct Henc as [H Henc]; rewrite <-?H in *
             end; rewrite <-?Henc in *;
      subst results; subst resultI; subst decodeI; subst opcode; subst funct3;
      subst funct5; subst funct6; subst funct7; subst funct10; subst funct12;
      repeat match goal with
      | H: False |- _ => destruct H
      | |- ?x = ?x => exact_no_check (eq_refl x)
      | |- _ => progress cbn_encode
      | |- _ => rewrite !Bool.orb_true_r in *
      | |- _ => rewrite !Bool.andb_false_r in *
      | |- _ => progress subst
      end);
     (* cases where bitSlice in goal and hyps do not match (but the encoded value is fully specified) *)
     cbv [funct7_SFENCE_VMA opcode_SYSTEM funct3_PRIV funct12_WFI funct12_MRET funct12_SRET funct12_URET funct12_EBREAK funct12_ECALL funct3_FENCE_I opcode_MISC_MEM isValidI] in *;
     repeat match goal with
            | |- ?x = ?x => exact_no_check (eq_refl x)
            | |- context [?x =? ?y] =>
              let H := fresh "H" in
              destruct (x =? y) eqn:H;
                apply Z.eqb_eq in H || apply Z.eqb_neq in H
            | _ => progress cbn in *
            end;
     exfalso;
     try match goal with H: _ <> _ |- _ => apply H; clear H end;
     somega).
Qed.
