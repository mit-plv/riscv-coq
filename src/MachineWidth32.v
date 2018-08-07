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


Instance MachineWidth32: MachineWidth (word 32) := {|
  add := @wplus 32;
  sub := @wminus 32;
  mul := @wmult 32;
  div x y := @ZToWord 32 (Z.div (wordToZ x) (wordToZ y));
  rem x y := @ZToWord 32 (Z.modulo (wordToZ x) (wordToZ y));
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
|}.
- constructor; intros.
  + rewrite ZToWord_0. apply wplus_unit.
  + apply wplus_comm.
  + apply wplus_assoc.
  + rewrite <- natToWord_Z_to_nat by (cbv; discriminate).
    apply wmult_unit.
  + apply wmult_comm.
  + apply wmult_assoc.
  + apply wmult_plus_distr.
  + rewrite ZToWord_0.
    rewrite! wminus_def.
    rewrite wplus_unit.
    reflexivity.
  + rewrite ZToWord_0.
    rewrite! wminus_def.
    rewrite wplus_unit.
    apply wminus_inv.
- constructor; intros.
  + reflexivity.
  + reflexivity.
  + apply ZToWord_plus.
  + apply ZToWord_minus.
  + apply ZToWord_mult.
  + rewrite ZToWord_0.
    rewrite wminus_wminusZ.
    unfold wminusZ, wordBinZ.
    rewrite wordToZ_wzero.
    rewrite (Z.sub_0_l (wordToZ (ZToWord 32 x))).
    destruct (wordToZ_ZToWord' 32 x) as [k E].
    rewrite E.
    rewrite Z.opp_sub_distr.
    rewrite ZToWord_Npow2_add_k'.
    reflexivity.
  + apply Z.eqb_eq in H. congruence.
- exact (@weqb_true_iff 32).
- intros.
  pose proof (@wordToZ_size' 31 a) as P.
  rewrite! pow2_S_z in P.
  exact P.
- intros.
  unfold uwordToZ.
  split.
  + apply N2Z.is_nonneg.
  + pose proof (wordToN_bound a) as P.
    apply N2Z.inj_lt in P.
    exact P.
- intros. rewrite ZToWord_plus. rewrite! ZToWord_wordToZ. reflexivity.
- intros. rewrite ZToWord_minus. rewrite! ZToWord_wordToZ. reflexivity.
- intros. rewrite ZToWord_mult. rewrite! ZToWord_wordToZ. reflexivity.
- intros. apply wordToZ_ZToWord.
  rewrite! pow2_S_z.
  assumption.
- intros. apply uwordToZ_ZToWord. assumption.
- intros.
  unfold uwordToZ.
  rewrite ZToWord_Z_of_N.
  apply NToWord_wordToN.
- intros. apply ZToWord_wordToZ.
- cbv. discriminate.
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
