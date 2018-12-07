Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Require Import coqutil.Word.Interface.
Require Import coqutil.Word.Properties.
Require coqutil.Word.Naive.
Require Import coqutil.Word.LittleEndian.
Require Import coqutil.Datatypes.HList.
Require Import riscv.Utility.
Local Open Scope Z_scope.

Section M.
  Variable sz: Z.
  Hypothesis bound: 8 <= sz.
  Lemma bound_8 : 0 < 8.  omega. Qed.
  Lemma bound_sz: 0 < sz. omega. Qed.
  Lemma bound_sz_le: 0 <= sz. omega. Qed.

  Instance byte: Interface.word 8 := Naive.word 8 bound_8.
  Instance byte_ok: word.ok byte := Naive.ok _ _.
  Instance word_sz: Interface.word sz := Naive.word sz bound_sz.
  Instance word_ok: word.ok word_sz := Naive.ok _ _.

  Set Refine Instance Mode.

  Definition TODO{T: Type}: T. Admitted.

  Instance MachineWidth_XLEN: MachineWidth word_sz := {|
    w8  := tuple byte 1;
    w16 := tuple byte 2;
    w32 := tuple byte 4;
    w64 := tuple byte 8;
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
    XLEN := sz;
    regToInt8 := split 1;
    regToInt16 := split 2;
    regToInt32 := split 4;
    regToInt64 := split 8;
    uInt8ToReg  := combine 1;
    uInt16ToReg := combine 2;
    uInt32ToReg := combine 4;
    uInt64ToReg := combine 8;
    int8ToReg  a := word.sextend  8 (combine 1 a);
    int16ToReg a := word.sextend 16 (combine 2 a);
    int32ToReg a := word.sextend 32 (combine 4 a);
    int64ToReg a := word.sextend 64 (combine 8 a);
    s32 := word.sextend 32;
    u32(x: word_sz) := word.of_Z ((word.unsigned x) mod 2 ^ 32);
    regToZ_signed := word.signed;
    regToZ_unsigned := word.unsigned;
    sll w n := word.of_Z (Z.shiftl (word.unsigned w) n);
    srl w n := word.of_Z (Z.shiftr (word.unsigned w) n);
    sra w n := word.of_Z (Z.shiftr (word.signed   w) n);
    ltu := word.ltu;
    divu := word.divu;
    remu := word.modu;
    maxSigned := word.of_Z (2 ^ (sz - 1) - 1);
    maxUnsigned := word.of_Z (2 ^ sz - 1);
    minSigned := word.of_Z (- 2 ^ (sz - 1));
    regToShamt5 x := (word.unsigned x) mod 2 ^ 5;
    regToShamt  x := (word.unsigned x) mod 2 ^ (Z.log2 sz);
    highBits x := word.of_Z (bitSlice x sz (2 * sz));
    ZToReg := word.of_Z;
    regRing := word.ring_theory bound_sz_le;
    ZToReg_morphism := word.ring_morph bound_sz_le;
  |}.
  all: intros.
  - apply TODO.
  - apply word.signed_range. omega.
  - apply word.unsigned_range. omega.
  - apply TODO.
  - apply TODO.
  - apply TODO.
  - rewrite word.signed_of_Z. unfold word.swrap. apply TODO.
  - apply word.unsigned_of_Z.
  - apply word.of_Z_unsigned.
  - apply TODO.
  - assumption.
  - (* the only lemma which seems reasonable to use here is word.signed_divs,
       but it doesn't apply *)
    apply TODO.
  - apply TODO.
  - apply TODO.
  - apply TODO.
  Defined.

End M.
