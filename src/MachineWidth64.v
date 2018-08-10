Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Require Import bbv.Word.
Require Import riscv.Utility.
Import Word.ConversionNotations.
Import Word.ArithmeticNotations.
Local Open Scope word_scope.
Local Open Scope Z_scope.


Instance MachineWidth64: MachineWidth (word 64) := {|
  add := @wplus 64;
  sub := @wminus 64;
  mul := @wmult 64;
  div := @wordBinZ Z.quot 64;
  rem := @wordBinZ Z.rem 64;
  negate := @wneg 64;
  signed_less_than a b := if wslt_dec a b then true else false;
  reg_eqb := @weqb 64;
  xor := @wxor 64;
  or := @wor 64;
  and := @wand 64;
  XLEN := 64;
  regToInt8 := split1 8 56;
  regToInt16 := split1 16 48;
  regToInt32 := split1 32 32;
  regToInt64 := id;
  uInt8ToReg x := zext x 56;
  uInt16ToReg x := zext x 48;
  uInt32ToReg x := zext x 32;
  uInt64ToReg := id;
  int8ToReg x := sext x 56;
  int16ToReg x := sext x 48;
  int32ToReg x := sext x 32;
  int64ToReg := id;
  s32 x := sext (split1 32 32 x) 32;
  u32 x := zext (split1 32 32 x) 32;
  regToZ_signed := @wordToZ 64;
  regToZ_unsigned := @uwordToZ 64;
  sll w n := wlshift w (Z.to_nat n);
  srl w n := wrshift w (Z.to_nat n);
  sra w n := wrshift w (Z.to_nat n);
  ltu a b := if wlt_dec a b then true else false;
  divu a b := ZToWord 64 (Z.quot (uwordToZ a) (uwordToZ b));
  remu a b := ZToWord 64 (Z.rem  (uwordToZ a) (uwordToZ b));
  maxSigned := combine (wones 63) (wzero 1);
  maxUnsigned := wones 64;
  minSigned := wpow2 63;
  regToShamt5 x := Z.of_N (wordToN (split1 5 59 x));
  regToShamt  x := Z.of_N (wordToN (split1 6 58 x));
  highBits x := ZToWord 64 (bitSlice x 64 128);
  ZToReg := ZToWord 64;
  regRing := @word_ring_theory_Z 64;
  ZToReg_morphism := @word_ring_morph_Z 64;
  reg_eqb_spec := @weqb_true_iff 64;
  regToZ_signed_bounds := @wordToZ_size'' 64 ltac:(lia);
  regToZ_unsigned_bounds := @uwordToZ_bound 64;
  add_def_signed := @wplus_Z 64;
  sub_def_signed := @wminus_Z 64;
  mul_def_signed := @wmult_Z 64;
  regToZ_ZToReg_signed := @wordToZ_ZToWord'' 64 ltac:(lia);
  regToZ_ZToReg_unsigned := @uwordToZ_ZToWord 64;
  ZToReg_regToZ_unsigned := @ZToWord_uwordToZ 64;
  ZToReg_regToZ_signed := @ZToWord_wordToZ 64;
  XLEN_lbound := ltac:(lia);
  div_def  _ _ := eq_refl;
  rem_def  _ _ := eq_refl;
  divu_def _ _ := eq_refl;
  remu_def _ _ := eq_refl;
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
