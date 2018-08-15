Require Import Coq.ZArith.ZArith.
Require Import Coq.Logic.ProofIrrelevance.
Require Import bbv.ZLib.
Require Import riscv.util.ZBitOps.
Require Import riscv.util.Tactics.
Require Import riscv.util.div_mod_to_quot_rem.
Local Open Scope Z_scope.


Definition word(sz: Z) := { x: Z | x mod 2 ^ sz = x }.

Definition ZToWord(sz: Z)(x: Z): word sz := 
  exist _ (x mod 2 ^ sz) (Zmod_mod x (2 ^ sz)).

Definition uwordToZ{sz: Z}: word sz -> Z := @proj1_sig Z (fun x => x mod 2 ^ sz = x).

Definition wmsb{sz: Z}(a: word sz): bool := Z.testbit (uwordToZ a) (sz - 1).

Definition swordToZ{sz: Z}(a: word sz): Z :=
  if wmsb a then uwordToZ a - 2 ^ sz else uwordToZ a.

Definition wu_unop(f: Z -> Z)(sz: Z)(a: word sz): word sz :=
  ZToWord sz (f (uwordToZ a)).

Definition wu_binop(f: Z -> Z -> Z)(sz: Z)(a b: word sz): word sz :=
  ZToWord sz (f (uwordToZ a) (uwordToZ b)).

Definition wu_binop_t{T: Type}(f: Z -> Z -> T)(sz: Z)(a b: word sz): T :=
  f (uwordToZ a) (uwordToZ b).

Definition ws_unop(f: Z -> Z)(sz: Z)(a: word sz): word sz :=
  ZToWord sz (f (swordToZ a)).

Definition ws_binop(f: Z -> Z -> Z)(sz: Z)(a b: word sz): word sz :=
  ZToWord sz (f (swordToZ a) (swordToZ b)).

Definition ws_binop_t{T: Type}(f: Z -> Z -> T)(sz: Z)(a b: word sz): T :=
  f (swordToZ a) (swordToZ b).

Hint Unfold ZToWord uwordToZ wmsb swordToZ
            wu_unop wu_binop wu_binop_t
            ws_unop ws_binop ws_binop_t
            proj1_sig
: unf_word_all.


Section ArithOps.

  Context {sz: Z}.

  Definition wopp := ws_unop Z.opp sz.

  Definition wadd := wu_binop Z.add sz.
  Definition wsub := wu_binop Z.sub sz.
  Definition wmul := wu_binop Z.mul sz.

  Definition wsadd := ws_binop Z.add sz.
  Definition wssub := ws_binop Z.sub sz.
  Definition wsmul := ws_binop Z.mul sz.

End ArithOps.

Hint Unfold wopp wadd wsub wmul wsadd wssub wsmul : unf_word_all.


Ltac make_mod_nonzero :=
  let C := fresh in
  match goal with
  | |- context [_ mod ?m] =>
    assert (m = 0 \/ m <> 0) as C by omega;
    destruct C as [C | C];
    [ rewrite C in *; rewrite? Zmod_0_r; reflexivity | ]
  end.

Ltac mod0_exists_quotient H :=
  apply Z.mod_divide in H;
  [ let k := fresh "k" in let E := fresh "E" in unfold Z.divide in H; destruct H as [k E] | ].  

Lemma mod_eq_from_diff: forall a b m,
    (a - b) mod m = 0 ->
    a mod m = b mod m.
Proof.
  intros.
  make_mod_nonzero.
  mod0_exists_quotient H; [|assumption].
  replace a with (b + k * m) by omega.
  apply Z_mod_plus_full.
Qed.

Lemma mod_eq_to_diff: forall a b m : Z,
    a mod m = b mod m ->
    (a - b) mod m = 0.
Proof.
  intros.
  make_mod_nonzero.
  apply Z.mod_divide; [assumption|].
  unfold Z.divide.
  div_mod_to_quot_rem.
  subst a b r0.
  exists (q - q0).
  ring.
Qed.

Ltac prove_mod_0 :=
  match goal with
  | |- ?a mod ?m = 0 => ring_simplify a
  end;
  rewrite? Zplus_mod_idemp_l;
  rewrite? Zplus_mod_idemp_r;
  rewrite? Zminus_mod_idemp_l;
  rewrite? Zminus_mod_idemp_r;
  rewrite? Zmult_mod_idemp_l;
  rewrite? Zmult_mod_idemp_r;
  match goal with
  | |- ?a mod ?m = 0 => ring_simplify a
  end;
  rewrite? Z.pow_2_r;
  first
    (* base cases: *)
    [ apply Z_mod_mult
    | apply Z_mod_mult'
    | apply Z_mod_same_full
    | apply Zmod_0_l
    (* cases with recursion (the last two might turn a true goal into a false one): *)
    | apply Z_mod_zero_opp_full
    | apply add_mod_0
    | apply sub_mod_0
 (* | match goal with
      | |- ?G => fail 1000 "failed to solve" G
      end *)
    ];
  [> prove_mod_0 .. ].

Ltac word_destruct :=
  intuition idtac;
  repeat autounfold with unf_word_all in *;
  repeat match goal with
         | w: word _ |- _ => let H := fresh "M" w in destruct w as [w H]
         end;
  repeat match goal with
         | H: (?x =? ?y) = true |- _ =>
           apply Z.eqb_eq in H; try subst x; try subst y
         | H: exist _ ?x _ = exist _ ?y _ |- _ =>
           apply EqdepFacts.eq_sig_fst in H; try subst x; try subst y
  end;
  repeat match goal with
         | |- context[if ?b then _ else _] => let E := fresh "E" in destruct b eqn: E
         end.

Ltac word_eq_pre :=
  repeat match goal with
         | H: ?a mod ?m = ?b mod ?m |- _ =>
           apply mod_eq_to_diff in H;
           match type of H with
           | ?a mod ?m = 0 => ring_simplify a in H
           end
         end;
  try apply subset_eq_compat;
  try apply Z.eqb_refl;
  auto;
  try match goal with
      | H: ?b mod ?m = ?b |- _  = ?b => refine (eq_trans _ H)
      end;
  try match goal with
      | H: ?a mod ?m = ?a |- ?a = _  => refine (eq_trans (eq_sym H) _)
      end;
  rewrite? Zplus_mod_idemp_l;
  rewrite? Zplus_mod_idemp_r;
  rewrite? Zminus_mod_idemp_l;
  rewrite? Zminus_mod_idemp_r;
  rewrite? Zmult_mod_idemp_l;
  rewrite? Zmult_mod_idemp_r;
  apply mod_eq_from_diff.

Ltac word_solver := word_destruct; word_eq_pre; prove_mod_0.


Section ArithOpsEquiv.

  Context {sz: Z}.

  Lemma wadd_wsadd: forall a b: word sz,
      wadd a b = wsadd a b.
  Proof. word_solver. Qed.

  Lemma wsub_wssub: forall a b: word sz,
      wsub a b = wssub a b.
  Proof. word_solver. Qed.

  Lemma wmul_wsmul: forall a b: word sz,
      wmul a b = wsmul a b.
  Proof. word_solver. Qed.

End ArithOpsEquiv.


Section MoreOps.

  Context {sz: Z}.

  Definition wudiv  := wu_binop Z.div sz.
  Definition wuquot := wu_binop Z.quot sz.
  Definition wumod  := wu_binop Z.modulo sz.
  Definition wurem  := wu_binop Z.rem sz.

  Definition wsdiv  := ws_binop Z.div sz.
  Definition wsquot := ws_binop Z.quot sz.
  Definition wsmod  := ws_binop Z.modulo sz.
  Definition wsrem  := ws_binop Z.rem sz.
  
  Definition wor   := wu_binop Z.lor sz.
  Definition wand  := wu_binop Z.land sz.
  Definition wxor  := wu_binop Z.lxor sz.

  Definition weqb := wu_binop_t Z.eqb sz.

  Definition wuleb := wu_binop_t Z.leb sz.
  Definition wultb := wu_binop_t Z.ltb sz.
  Definition wugeb := wu_binop_t Z.geb sz.
  Definition wugtb := wu_binop_t Z.gtb sz.

  Definition wsleb := ws_binop_t Z.leb sz.
  Definition wsltb := ws_binop_t Z.ltb sz.
  Definition wsgeb := ws_binop_t Z.geb sz.
  Definition wsgtb := ws_binop_t Z.gtb sz.

  Definition wshiftl  := wu_binop Z.shiftl sz.
  Definition wshiftr  := wu_binop Z.shiftr sz.
  Definition wshiftra := ws_binop Z.shiftr sz.

End MoreOps.

Hint Unfold
    wudiv wuquot wumod wurem
    wsdiv wsquot wsmod wsrem
    wor wand wxor
    weqb
    wuleb wultb wugeb wugtb
    wsleb wsltb wsgeb wsgtb
    wshiftl wshiftr wshiftra
: unf_word_all.


Definition wucast{sz: Z}(sz': Z)(w: word sz): word sz' :=
  ZToWord sz' (uwordToZ w).

Definition wscast{sz: Z}(sz': Z)(w: word sz): word sz' :=
  ZToWord sz' (swordToZ w).

(*
Definition wappend{sz1 sz2: Z}(w1: word sz1)(w2: word sz2): word (sz1 + sz2) :=
  ZToWord (sz1 + sz2) (2 ^ sz2 * (uwordToZ w1) + uwordToZ w2).
*)
Definition wappend{sz1 sz2: Z}(w1: word sz1)(w2: word sz2): word (sz1 + sz2) :=
  ZToWord (sz1 + sz2) (Z.lor (2 ^ sz2 * (uwordToZ w1)) (uwordToZ w2)).

(*
Definition wslice{sz: Z}(w: word sz)(i j: Z): word (j - i) :=
  ZToWord (j - i) (bitSlice (uwordToZ w) i j).

Definition lobits(sz: Z)(w: word (2 * sz)): word sz.
  wslice w sz (2 * sz).

Definition hibits(sz: Z)(w: word (2 * sz)): word sz :=
  ZToWord sz (bitSlice (uwordToZ w) sz (2 * sz)).

Definition wslice(sz1 sz2 sz3: Z)(w: word (sz1 + sz2 + sz3)): word sz2 :=
  ZToWord sz2 (bitSlice (uwordToZ w) sz1 (sz1 + sz2)).
 *)

Definition wsplit_lo(sz1 sz2: Z)(w: word (sz1 + sz2)): word sz2 :=
  wucast sz2 w.

Definition wsplit_hi(sz1 sz2: Z)(w: word (sz1 + sz2)): word sz1 :=
  ZToWord sz1 (Z.shiftr (uwordToZ w) sz2).

Definition lobits(sz: Z)(w: word (sz + sz)): word sz := wsplit_lo sz sz w.

Definition hibits(sz: Z)(w: word (sz + sz)): word sz := wsplit_hi sz sz w.

Hint Unfold wucast wscast wappend wsplit_lo wsplit_hi lobits hibits : unf_word_all.

Ltac word_omega_pre :=
      repeat match goal with
         | n: Z |- _ => 
           let B := fresh in assert (0 < n) by omega;
           unique pose proof (pow2_times2 n B)
         | _: context[2 ^ ?n] |- _ =>
           let B := fresh in assert (0 <= n) by omega;
           unique pose proof (pow2_pos n B)
         | _: context[?a mod ?m] |- _ =>
           let B := fresh in assert (0 < m) by omega;
           unique pose proof (Z.mod_pos_bound a m B)
         | H: ?a mod 2 ^ _ = ?a      |- _ => apply mod_pow2_same_bounds in H; [|omega]
         | H: Z.testbit _ _ = true   |- _ => apply testbit_true_nonneg in H; [|omega..]
         | H: Z.testbit _ _ = false  |- _ => apply testbit_false_nonneg in H; [|omega..]
         | H1: ?a <= ?b, H2: ?b < ?c  |- _ => unique pose proof (conj H1 H2)
         | H: - 2 ^ _ <= ?n < 2 ^ _   |- _ => unique pose proof (signed_bounds_to_sz_pos _ _ H)
         end.

Ltac word_omega := word_omega_pre; omega.

Lemma word_eq_bitwise: forall sz (a b: word sz),
    (forall i, 0 <= i < sz -> Z.testbit (uwordToZ a) i = Z.testbit (uwordToZ b) i) ->
    a = b.
Proof.
  word_destruct.
  apply subset_eq_compat.
  assert (sz < 0 \/ sz = 0 \/ 0 < sz) as C by omega. destruct C as [C | [C | C]].
  - rewrite Z.pow_neg_r in * by assumption.
    rewrite Zmod_0_r in *.
    congruence.
  - subst. change (2 ^ 0) with 1 in *.
    rewrite Zmod_1_r in *.
    congruence.
  - 
Abort.

Lemma wappend_split: forall sz1 sz2 (w : word (sz1 + sz2)),
    wappend (wsplit_hi sz1 sz2 w) (wsplit_lo sz1 sz2 w) = w.
Proof.
   word_destruct. apply subset_eq_compat.
   rewrite <-? Z.land_ones.
Admitted.

Lemma wappend_inj: forall sz1 sz2 (a : word sz1) (b : word sz2) (c : word sz1) (d : word sz2),
    0 <= sz1 ->
    0 <= sz2 ->
    wappend a b = wappend c d ->
    a = c /\ b = d.
Proof.
  word_destruct; word_eq_pre.
  - mod0_exists_quotient H1; [|word_omega].
    replace (2 ^ sz2 * a - 2 ^ sz2 * c + b - d) with
            (b - d + (a - c) * (2 ^ sz2)) in E by ring.
    rewrite Z.pow_add_r in E by omega.
Admitted.

Lemma word_ring: forall sz,
    ring_theory (ZToWord sz 0) (ZToWord sz 1) wadd wmul wsub wopp eq.
Proof.
  intros. constructor; word_solver.
Qed.

Lemma word_ring_morph_Z: forall sz,
    ring_morph (ZToWord sz 0) (ZToWord sz 1) wadd  wmul  wsub  wopp  eq
               0              1              Z.add Z.mul Z.sub Z.opp Z.eqb
               (ZToWord sz).
Proof.
  intros. constructor; word_solver.
Qed.

Lemma weqb_spec: forall sz (a b : word sz),
    weqb a b = true <-> a = b.
Proof. word_solver. Qed.

Lemma swordToZ_bound: forall sz (a : word sz),
    0 < sz ->
    - 2 ^ (sz - 1) <= swordToZ a < 2 ^ (sz - 1).
Proof. word_destruct; word_omega. Qed.

Lemma uwordToZ_bound: forall sz (a : word sz),
    0 < sz ->
    0 <= uwordToZ a < 2 ^ sz.
Proof. word_destruct; word_omega. Qed.

Lemma swordToZ_ZToWord: forall sz n,
    - 2 ^ (sz - 1) <= n < 2 ^ (sz - 1) ->
    swordToZ (ZToWord sz n) = n.
Proof.
  word_destruct; word_omega_pre;
    assert (sz = 1 \/ 1 < sz) as C by omega;
    (destruct C as [C | C];
     [subst sz;
      repeat match goal with
             | _: context[2 ^ ?x] |- _ =>
               let r := eval cbv in (2 ^ x) in change (2 ^ x) with r in *
             end;
      assert (n = -1 \/ n = 0) as C by omega;
      destruct C; subst n; cbv in E; try reflexivity; congruence |]);
      match goal with
        | _: context[?a mod ?m] |- _ =>
          let B := fresh in
          assert (m <> 0) by omega;
          pose proof (Z.mod_eq a m B) as M
        end;
      assert (- 2 ^ (sz - 1) <= n <= 2 ^ (sz - 1) + 1) as B by omega;
      (apply (range_div_pos _ _ _ (2 ^ sz)) in B; [|omega]);
      assert (2 ^ (sz - 1) mod 2 ^ sz = 2 ^ (sz - 1)) by (apply Z.mod_small; omega);
      rewrite Z.div_opp_l_nz in B by omega;
      rewrite Z.div_small in B by omega;
      (rewrite (Z.div_small (2 ^ (sz - 1) + 1) (2 ^ sz)) in B;
       [ assert (n / 2 ^ sz = 0 \/ n / 2 ^ sz = -1) as R by omega;
         destruct R as [R | R]; rewrite R in M; omega
       | split; try omega;
         rewrite H4;
         pose proof (Z.pow_gt_1 2 (sz - 1));
         omega ]).
Qed.

Lemma uwordToZ_ZToWord_mod: forall sz n,
    uwordToZ (ZToWord sz n) = n mod 2 ^ sz.
Proof. intros. reflexivity. Qed.

Lemma ZToWord_uwordToZ: forall sz (a : word sz),
    ZToWord sz (uwordToZ a) = a.
Proof. word_solver. Qed.

Lemma ZToWord_swordToZ: forall sz (a : word sz),
    ZToWord sz (swordToZ a) = a.
Proof. word_solver. Qed.
