Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Require Import riscv.util.Word.
Require Import riscv.Utility.
Local Open Scope Z_scope.

Instance MachineWidth_XLEN(sz: Z)(bound: 8 <= sz): MachineWidth (word sz) := {|
  add := @wadd sz;
  sub := @wsub sz;
  mul := @wmul sz;
  div := @wsquot sz;
  rem := @wsrem sz;
  negate := @wopp sz;
  signed_less_than := @wsltb sz;
  reg_eqb := @weqb sz;
  xor := @wxor sz;
  or := @wor sz;
  and := @wand sz;
  XLEN := sz;
  regToInt8  := wscast 8;
  regToInt16 := wscast 16;
  regToInt32 := wscast 32;
  regToInt64 := wscast 64;
  uInt8ToReg  := wucast sz;
  uInt16ToReg := wucast sz;
  uInt32ToReg := wucast sz;
  uInt64ToReg := wucast sz;
  int8ToReg  := wscast sz;
  int16ToReg := wscast sz;
  int32ToReg := wscast sz;
  int64ToReg := wscast sz;
  s32(x: word sz) := wscast sz (wscast 32 x);
  u32(x: word sz) := wucast sz (wucast 32 x);
  regToZ_signed := @swordToZ sz;
  regToZ_unsigned := @uwordToZ sz;
  sll w n := ZToWord sz (Z.shiftl (uwordToZ w) n);
  srl w n := ZToWord sz (Z.shiftr (uwordToZ w) n);
  sra w n := ZToWord sz (Z.shiftr (swordToZ w) n);
  ltu := @wultb sz;
  divu := @wuquot sz;
  remu := @wurem sz;
  maxSigned := ZToWord sz (2 ^ (sz - 1) - 1);
  maxUnsigned := ZToWord sz (2 ^ sz - 1);
  minSigned := ZToWord sz (- 2 ^ (sz - 1));
  regToShamt5 x := (uwordToZ x) mod 2 ^ 5;
  regToShamt  x := (uwordToZ x) mod 2 ^ (Z.log2 sz);
  highBits x := ZToWord sz (bitSlice x sz (2 * sz));
  ZToReg := ZToWord sz;
  regRing := @word_ring sz;
  ZToReg_morphism := @word_ring_morph_Z sz;
  reg_eqb_spec := @weqb_spec sz;
  regToZ_signed_bounds   _ := @swordToZ_bound sz _ ltac:(lia);
  regToZ_unsigned_bounds _ := @uwordToZ_bound sz _ ltac:(lia);
  add_def_signed := @wadd_wsadd sz;
  sub_def_signed := @wsub_wssub sz;
  mul_def_signed := @wmul_wsmul sz;
  regToZ_ZToReg_signed := @swordToZ_ZToWord sz;
  regToZ_ZToReg_unsigned_mod := @uwordToZ_ZToWord sz;
  ZToReg_regToZ_unsigned := @ZToWord_uwordToZ sz;
  ZToReg_regToZ_signed := @ZToWord_swordToZ sz;
  XLEN_lbound := bound;
  div_def  _ _ := eq_refl;
  rem_def  _ _ := eq_refl;
  divu_def _ _ := eq_refl;
  remu_def _ _ := eq_refl;  
|}.
