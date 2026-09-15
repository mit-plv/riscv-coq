Require Import Coq.ZArith.ZArith.
Require Import coqutil.Word.Bitwidth.
Require Import coqutil.Word.LittleEndianList.
Require Import coqutil.Datatypes.HList.
Require Import  riscv.Utility.Utility.
Local Open Scope Z_scope.

#[global] Instance MachineWidth_XLEN{width}{BW: Bitwidth width}: MachineWidth (bits width) := {|
  add := Zmod.add;
  sub := Zmod.sub;
  mul := Zmod.mul;
  div := Zmod.squot;
  rem := Zmod.srem;
  negate := Zmod.opp;
  signed_less_than a b := Z.ltb (Zmod.signed a) (Zmod.signed b);
  reg_eqb := Zmod.eqb;
  xor := Zmod.xor;
  or := Zmod.or;
  and := Zmod.and;
  XLEN := width;
  regToInt8  a := tuple.of_list (le_split 1 (Zmod.unsigned a));
  regToInt16 a := tuple.of_list (le_split 2 (Zmod.unsigned a));
  regToInt32 a := tuple.of_list (le_split 4 (Zmod.unsigned a));
  regToInt64 a := tuple.of_list (le_split 8 (Zmod.unsigned a));
  uInt8ToReg  a := bits.of_Z _ (le_combine (tuple.to_list a));
  uInt16ToReg a := bits.of_Z _ (le_combine (tuple.to_list a));
  uInt32ToReg a := bits.of_Z _ (le_combine (tuple.to_list a));
  uInt64ToReg a := bits.of_Z _ (le_combine (tuple.to_list a));
  int8ToReg  a := bits.of_Z _ (signExtend  8 (le_combine (tuple.to_list a)));
  int16ToReg a := bits.of_Z _ (signExtend 16 (le_combine (tuple.to_list a)));
  int32ToReg a := bits.of_Z _ (signExtend 32 (le_combine (tuple.to_list a)));
  int64ToReg a := bits.of_Z _ (signExtend 64 (le_combine (tuple.to_list a)));
  s32 x := bits.of_Z _ (signExtend 32 (Zmod.unsigned x));
  u32 x := bits.of_Z _ ((Zmod.unsigned x) mod 2 ^ 32);
  regToZ_signed := Zmod.signed;
  regToZ_unsigned := Zmod.unsigned;
  sll := Zmod.slu;
  srl := Zmod.sru;
  sra := Zmod.srs;
  ltu a b := Z.ltb (Zmod.unsigned a) (Zmod.unsigned b);
  divu := Zmod.udiv;
  remu := Zmod.umod;
  maxSigned := bits.of_Z _ (2 ^ (width - 1) - 1);
  maxUnsigned := bits.of_Z _ (2 ^ width - 1);
  minSigned := bits.of_Z _ (- 2 ^ (width - 1));
  regToShamt5 x := (Zmod.unsigned x) mod 2 ^ 5;
  regToShamt  x := (Zmod.unsigned x) mod 2 ^ (Z.log2 width);
  highBits x := bits.of_Z _ (bitSlice x width (2 * width));
  ZToReg := Zmod.of_Z (2 ^ width);
|}.
