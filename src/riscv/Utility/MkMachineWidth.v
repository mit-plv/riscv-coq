Require Import Coq.ZArith.ZArith.
Require Import coqutil.Word.Interface.
Require Import coqutil.Z.BitOps.
Require Import coqutil.Word.LittleEndian.
Require Import coqutil.Datatypes.HList.
Require Import riscv.Utility.Utility.
Local Open Scope Z_scope.

#[global] Instance MachineWidth_XLEN{width}{_: Bitwidth width}{word: word width}: MachineWidth word := {|
  add := word.add;
  sub := word.sub;
  mul := word.mul;
  div := word.divs;
  rem := word.mods;
  negate := word.opp;
  signed_less_than := word.lts;
  reg_eqb := word.eqb;
  xor := word.xor;
  or := word.or;
  and := word.and;
  XLEN := width;
  regToInt8  a := split 1 (word.unsigned a);
  regToInt16 a := split 2 (word.unsigned a);
  regToInt32 a := split 4 (word.unsigned a);
  regToInt64 a := split 8 (word.unsigned a);
  uInt8ToReg  a := word.of_Z (combine 1 a);
  uInt16ToReg a := word.of_Z (combine 2 a);
  uInt32ToReg a := word.of_Z (combine 4 a);
  uInt64ToReg a := word.of_Z (combine 8 a);
  int8ToReg  a := word.of_Z (signExtend  8 (combine 1 a));
  int16ToReg a := word.of_Z (signExtend 16 (combine 2 a));
  int32ToReg a := word.of_Z (signExtend 32 (combine 4 a));
  int64ToReg a := word.of_Z (signExtend 64 (combine 8 a));
  s32 := word.sextend 32;
  u32(x: word) := word.of_Z ((word.unsigned x) mod 2 ^ 32);
  regToZ_signed := word.signed;
  regToZ_unsigned := word.unsigned;
  sll w n := word.slu w (word.of_Z n);
  srl w n := word.sru w (word.of_Z n);
  sra w n := word.srs w (word.of_Z n);
  ltu := word.ltu;
  divu := word.divu;
  remu := word.modu;
  maxSigned := word.of_Z (2 ^ (width - 1) - 1);
  maxUnsigned := word.of_Z (2 ^ width - 1);
  minSigned := word.of_Z (- 2 ^ (width - 1));
  regToShamt5 x := (word.unsigned x) mod 2 ^ 5;
  regToShamt  x := (word.unsigned x) mod 2 ^ (Z.log2 width);
  highBits x := word.of_Z (bitSlice x width (2 * width));
  ZToReg := word.of_Z;
|}.
