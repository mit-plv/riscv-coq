Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Require Import bbv.Word.
Require Import riscv.Utility.
Import Word.ConversionNotations.
Import Word.ArithmeticNotations.
Local Open Scope word_scope.
Local Open Scope Z_scope.

Lemma NToWord_plus: forall sz (n m : N), NToWord sz (n + m) = NToWord sz n ^+ NToWord sz m.
Admitted.

Lemma NToWord_inj: forall sz (n m: N),
    NToWord sz n = NToWord sz m ->
    (n < Npow2 sz)%N ->
    (m < Npow2 sz)%N ->
    n = m.
Admitted.

Ltac Nify_one n :=
    rewrite <- (NToWord_wordToN n) in *;
    let B := fresh "B" in
    pose proof (wordToN_bound n) as B;
    rewrite (wordToN_NToWord_2 _ B) in *;
    let E := fresh "E" in
    let n' := fresh n in
    remember (wordToN n) as n' eqn: E;
    clear E n;
    rename n' into n.

Ltac Nify :=
  repeat match goal with
  | n: word _ |- _ => Nify_one n
  end.

Definition TODO{T: Type}: T. Admitted.

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
  regToZ_ZToReg_signed := @wordToZ_ZToWord'' 32 ltac:(lia);
  regToZ_ZToReg_unsigned := @uwordToZ_ZToWord 32;
  ZToReg_regToZ_unsigned := @ZToWord_uwordToZ 32;
  ZToReg_regToZ_signed := @ZToWord_wordToZ 32;
  XLEN_lbound := ltac:(lia);
|}.
all: intros.
- split.
  + unfold wdiv, wmod, wmult, wordBin.
    rewrite wordToN_NToWord_2 by apply TODO.
    rewrite <- NToWord_plus.
    rewrite <- (N.div_mod' (wordToN a) (wordToN b)).
    rewrite NToWord_wordToN.
    reflexivity.
  + split.
    * pose proof uwordToZ_bound as P.
      (* automation_challenge *)
      specialize (P 32%nat (a ^% b)). intuition idtac.
    * unfold uwordToZ.
      apply N2Z.inj_lt.
      unfold wmod, wordBin.
      assert (wordToN a mod wordToN b < wordToN b)%N. {
        apply N.mod_upper_bound. rewrite ZToWord_0 in H. apply wordToN_neq_0. assumption.
      }
      rewrite wordToN_NToWord_2; [assumption|].
      eapply N.lt_trans; [eassumption|].
      apply wordToN_bound.
- unfold wdiv, wmod, wmult, wordBin, uwordToZ in *.
  Nify.
  destruct H0 as [E [_ R]].
  apply N2Z.inj_lt in R.
  rewrite <- NToWord_plus in E.
  apply NToWord_inj in E.
  + split; f_equal.
    * apply N.div_unique in E; assumption.
    * apply N.mod_unique in E; assumption.
  + assumption.
  + apply TODO. (* does not hold!

  uniqueness of div does not hold on word:
  Example with sz = 4 (i.e. everything is modulo 16).

  Given a=13, b=8, there are several ways to satisfy the equation
  a  = b * q + r    0 <= r < b
  13 = 8 * 1 + 5    0 <= 5 < 8
  13 = 8 * 3 + 5    0 <= 5 < 8
  13 = 8 * 5 + 5    0 <= 5 < 8
  etc

  uniqueness of mod does not hold either:

  Given a=13, b=14, there are several ways to satisfy the equation
  a  =  b * q +  r    0 <=  r <  b
  13 = 14 * 0 + 13    0 <= 13 < 14
  13 = 14 * 3 +  3    0 <=  3 < 14
  
  a = b * q + r    0 <= r < b
  
  3 = 8 * 8 + 3    0 <= 3 < 8
 *)
Defined.

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
