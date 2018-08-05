Require Import Coq.ZArith.BinInt.
Require Import bbv.Word.
Require Import riscv.Utility.
Import Word.ConversionNotations.
Local Open Scope word_scope.

Definition TODO{T: Type}: T. Admitted.

Instance MachineWidth64: MachineWidth (word 64) := {|
  add := @wplus 64;
  sub := @wminus 64;
  mul := @wmult 64;
  div x y := @ZToWord 64 (Z.div (wordToZ x) (wordToZ y));
  rem x y := @ZToWord 64 (Z.modulo (wordToZ x) (wordToZ y));
  signed_less_than a b := if wslt_dec a b then true else false;
  signed_eqb := @weqb 64;
  xor := @wxor 64;
  or := @wor 64;
  and := @wand 64;
  XLEN := 64;
  fromImm := ZToWord 64;
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
  divu := @wdiv 64;
  remu := @wmod 64;
  maxSigned := combine (wones 63) (wzero 1);
  maxUnsigned := wones 64;
  minSigned := wones 64;
  regToShamt5 x := Z.of_N (wordToN (split1 5 59 x));
  regToShamt  x := Z.of_N (wordToN (split1 6 58 x));
  highBits x := ZToWord 64 (bitSlice x 64 128);
  ZToReg := ZToWord 64;
|}.
all: apply TODO.
Defined.

(* Tests that all operations reduce under cbv.
   If something prints a huge term with unreduced matches in it, running small examples
   inside Coq will not work! *)
(*
Eval cbv in zero.
Eval cbv in one.
Eval cbv in add $7 $9.
Eval cbv in sub $11 $4.
Eval cbv in mul $16 $4.
Eval cbv in div $100 $8.
Eval cbv in rem $100 $8.
Eval cbv in signed_less_than $4 $5.
Eval cbv in signed_eqb $7 $9.
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
*)
