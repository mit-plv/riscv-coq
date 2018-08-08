Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Require Import bbv.Word.
Require Import riscv.Utility.
Import Word.ConversionNotations.
Import Word.ArithmeticNotations.
Local Open Scope word_scope.
Local Open Scope Z_scope.


Lemma ZToWord_Npow2_add_k':  forall sz z k,
    ZToWord sz (z + k * Z.of_N (Npow2 sz)) = ZToWord sz z.
Proof.
  intros. assert (0 <= k \/ k < 0) as C by lia. destruct C as [C | C].
  - pose proof (ZToWord_Npow2_add_k sz z (Z.to_nat k)) as Q.
    rewrite Znat.Z2Nat.id in Q; assumption.
  - pose proof (ZToWord_Npow2_sub_k sz z (Z.to_nat (- k))) as Q.
    rewrite Znat.Z2Nat.id in Q by lia.
    rewrite <- Q.
    f_equal.
    lia.
Qed.    

Lemma wneg_0_wminus: forall {sz: nat} (x: word sz),
    ^~ x = $0 ^- x.
Proof.
  intros.
  rewrite <- wplus_unit at 1.
  reflexivity.
Qed.

Lemma ZToWord_opp_wneg{sz: nat}: forall (x: Z),
    ZToWord sz (- x) = ^~ (ZToWord sz x).
Proof.
  intros.
  rewrite wneg_0_wminus.
  rewrite wminus_wminusZ.
  unfold wminusZ, wordBinZ.
  rewrite wordToZ_wzero.
  rewrite (Z.sub_0_l (wordToZ (ZToWord sz x))).
  destruct (wordToZ_ZToWord' sz x) as [k E].
  rewrite E.
  rewrite Z.opp_sub_distr.
  rewrite ZToWord_Npow2_add_k'.
  reflexivity.
Qed.

Lemma ZToWord_1{sz : nat}: ZToWord sz 1 = wone sz.
Proof.
  intros.
  rewrite <- natToWord_Z_to_nat by (cbv; discriminate).  
  reflexivity.
Qed.

Lemma Zeqb_true_ZToWord: forall {sz: nat} (x y: Z),
    (x =? y) = true ->
    ZToWord sz x = ZToWord sz y.
Proof.
  intros. apply Z.eqb_eq in H. congruence.
Qed.

Lemma wordToZ_size'': forall (sz : nat),
    (0 < sz)%nat ->
    forall  (w : word sz), - 2 ^ (Z.of_nat sz - 1) <= wordToZ w < 2 ^ (Z.of_nat sz - 1).
Proof.
  intros.
  destruct sz; [lia|].
  pose proof (@wordToZ_size' sz w) as P.
  replace (Z.of_nat (S sz) - 1) with (Z.of_nat sz) by lia.
  rewrite Nat2Z_inj_pow in P.
  exact P.
Qed.

Lemma wordToZ_ZToWord': forall (sz: nat),
    (0 < sz)%nat ->
    forall n: Z,
      - 2 ^ (Z.of_nat sz - 1) <= n < 2 ^ (Z.of_nat sz - 1) ->
      wordToZ (ZToWord sz n) = n.
Proof.
  intros.
  destruct sz; [lia|].
  apply wordToZ_ZToWord.
  replace (Z.of_nat (S sz) - 1) with (Z.of_nat sz) in * by lia.
  rewrite Nat2Z_inj_pow.
  assumption.
Qed.

Lemma wplus_Z:  forall sz (a b : word sz),
    a ^+ b = ZToWord sz (wordToZ a + wordToZ b).
Proof.
  intros. rewrite ZToWord_plus. rewrite! ZToWord_wordToZ. reflexivity.
Qed.

Lemma wminus_Z: forall sz (a b : word sz),
    a ^- b = ZToWord sz (wordToZ a - wordToZ b).
Proof.
  intros. rewrite ZToWord_minus. rewrite! ZToWord_wordToZ. reflexivity.
Qed.

Lemma wmult_Z:  forall sz (a b : word sz),
    a ^* b = ZToWord sz (wordToZ a * wordToZ b).
Proof.
  intros. rewrite ZToWord_mult. rewrite! ZToWord_wordToZ. reflexivity.
Qed.

Lemma Z_of_N_Npow2: forall n, Z.of_N (Npow2 n) = 2 ^ Z.of_nat n.
Proof.
  intros.
  rewrite pow2_N.
  rewrite nat_N_Z.
  rewrite Nat2Z_inj_pow.
  reflexivity.
Qed.

Lemma uwordToZ_bound: forall sz (a: word sz),
    0 <= uwordToZ a < 2 ^ Z.of_nat sz.
Proof.
  intros.
  unfold uwordToZ.
  split.
  + apply N2Z.is_nonneg.
  + pose proof (wordToN_bound a) as P.
    apply N2Z.inj_lt in P.
    rewrite Z_of_N_Npow2 in P.
    assumption.
Qed.

Lemma ZToWord_uwordToZ: forall sz (a: word sz),
    ZToWord sz (uwordToZ a) = a.
Proof.
  intros.
  unfold uwordToZ.
  rewrite ZToWord_Z_of_N.
  apply NToWord_wordToN.  
Qed.

Lemma word_ring_theory_Z: forall (sz: nat),
    ring_theory (ZToWord sz 0) (ZToWord sz 1)
                (@wplus sz) (@wmult sz) (@wminus sz) (@wneg sz) eq.
Proof.
  intros.
  rewrite ZToWord_0.
  rewrite ZToWord_1.
  apply wring.
Qed.

Lemma word_ring_morph_Z: forall (sz: nat),
    ring_morph (ZToWord sz 0) (ZToWord sz 1) (@wplus sz) (@wmult sz) (@wminus sz) (@wneg sz)
               eq 0 1 Z.add Z.mul Z.sub Z.opp Z.eqb
               (ZToWord sz).
Proof.
  constructor.
  + reflexivity.
  + reflexivity.
  + exact (@ZToWord_plus sz).
  + exact (@ZToWord_minus sz).
  + exact (@ZToWord_mult sz).
  + exact (@ZToWord_opp_wneg sz).
  + exact (@Zeqb_true_ZToWord sz).
Qed.

Instance MachineWidth32: MachineWidth (word 32) := {|
  add := @wplus 32;
  sub := @wminus 32;
  mul := @wmult 32;
  div x y := @ZToWord 32 (Z.div (wordToZ x) (wordToZ y));
  rem x y := @ZToWord 32 (Z.modulo (wordToZ x) (wordToZ y));
  negate := @wneg 32;
  signed_less_than a b := if wslt_dec a b then true else false;
  reg_eqb := @weqb 32;
  xor := @wxor 32;
  or := @wor 32;
  and := @wand 32;
  XLEN := 32;
  regToInt8 := split1 8 24;
  regToInt16 := split1 16 16;
  regToInt32 := id;
  regToInt64 x := combine x (wzero 32);
  uInt8ToReg x := zext x 24;
  uInt16ToReg x := zext x 16;
  uInt32ToReg := id;
  uInt64ToReg := split1 32 32; (* unused *)
  int8ToReg x := sext x 24;
  int16ToReg x := sext x 16;
  int32ToReg := id;
  int64ToReg := split1 32 32; (* unused *)
  s32 := id;
  u32 := id;
  regToZ_signed := @wordToZ 32;
  regToZ_unsigned := @uwordToZ 32;
  sll w n := wlshift w (Z.to_nat n);
  srl w n := wrshift w (Z.to_nat n);
  sra w n := wrshift w (Z.to_nat n);
  ltu a b := if wlt_dec a b then true else false;
  divu := @wdiv 32;
  remu := @wmod 32;
  maxSigned := combine (wones 31) (wzero 1);
  maxUnsigned := wones 32;
  minSigned := wones 32;
  regToShamt5 x := Z.of_N (wordToN (split1 5 27 x));
  regToShamt  x := Z.of_N (wordToN (split1 5 27 x));
  highBits x := ZToWord 32 (bitSlice x 32 64);
  ZToReg := ZToWord 32;
  regRing := @word_ring_theory_Z 32;
  ZToReg_morphism := @word_ring_morph_Z 32;
  reg_eqb_spec := @weqb_true_iff 32;
  regToZ_signed_bounds := @wordToZ_size'' 32 ltac:(lia);
  regToZ_unsigned_bounds := @uwordToZ_bound 32;
  add_def_signed := @wplus_Z 32;
  sub_def_signed := @wminus_Z 32;
  mul_def_signed := @wmult_Z 32;
  regToZ_ZToReg_signed := @wordToZ_ZToWord' 32 ltac:(lia);
  regToZ_ZToReg_unsigned := @uwordToZ_ZToWord 32;
  ZToReg_regToZ_unsigned := @ZToWord_uwordToZ 32;
  ZToReg_regToZ_signed := @ZToWord_wordToZ 32;
  XLEN_lbound := ltac:(lia);
|}.

Goal False.
  idtac "Testing that all operations reduce under cbv."
        "If something prints a huge term with unreduced matches in it,"
        "running small examples inside Coq will not work!".
Abort.

Eval cbv in add $7 $9.
Eval cbv in sub $11 $4.
Eval cbv in mul $16 $4.
Eval cbv in div $100 $8.
Eval cbv in rem $100 $8.
Eval cbv in negate $8.
Eval cbv in signed_less_than $4 $5.
Eval cbv in reg_eqb $7 $9.
Eval cbv in xor $8 $11.
Eval cbv in or $3 $8.
Eval cbv in and $7 $19.
Eval cbv in fromImm 13%Z.
Eval cbv in regToInt8 $5.
Eval cbv in regToInt16 $5.
Eval cbv in regToInt32 $5.
Eval cbv in regToInt64 $5.
Eval cbv in uInt8ToReg $5.
Eval cbv in uInt16ToReg $5.
Eval cbv in uInt32ToReg $5.
Eval cbv in uInt64ToReg $5.
Eval cbv in int8ToReg $5.
Eval cbv in int16ToReg $5.
Eval cbv in int32ToReg $5.
Eval cbv in int64ToReg $5.
Eval cbv in s32 $5.
Eval cbv in u32 $5.
Eval cbv in regToZ_signed $5.
Eval cbv in regToZ_unsigned $5.
Eval cbv in sll $5 7.
Eval cbv in srl $5 7.
Eval cbv in sra $5 7.
Eval cbv in ltu $5 $7.
Eval cbv in divu $50 $8.
Eval cbv in remu $50 $8.
Eval cbv in maxSigned.
Eval cbv in maxUnsigned.
Eval cbv in minSigned.
Eval cbv in regToShamt5 $12.
Eval cbv in regToShamt $12.
Eval cbv in highBits (-9).
