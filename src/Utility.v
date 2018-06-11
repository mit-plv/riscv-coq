Require Import Coq.ZArith.BinInt.
Require Import bbv.Word.
Require Import bbv.DepEqNat.
Require Import riscv.util.Monads.
Require Import riscv.RiscvBitWidths.
Require Export riscv.util.ZBitOps.

(* Meaning of MachineInt: an integer big enough to hold an integer of a RISCV machine,
   no matter whether it's a 32-bit or 64-bit machine. *)
Definition MachineInt := Z.

Class MachineWidth(t: Set) := mkMachineWidth {
  (* constants *)
  zero: t;
  one: t;

  (* arithmetic operations (inherited from Integral in Haskell) *)
  add: t -> t -> t;
  sub: t -> t -> t;
  mul: t -> t -> t;
  div: t -> t -> t;
  rem: t -> t -> t;

  (* comparison operators (inherited from Eq and Ord in Haskell) *)
  signed_less_than: t -> t -> bool;
  signed_eqb: t -> t -> bool;

  (* logical operations (inherited from Bits in Haskell) *)
  xor: t -> t -> t;
  or: t -> t -> t;
  and: t -> t -> t;

  (* operations also defined in MachineWidth in Haskell: *)

  fromImm: MachineInt -> t;

  regToInt8: t -> word 8;
  regToInt16: t -> word 16;
  regToInt32: t -> word 32;
  regToInt64: t -> word 64;

  uInt8ToReg: word 8 -> t;
  uInt16ToReg: word 16 -> t;
  uInt32ToReg: word 32 -> t;
  uInt64ToReg: word 64 -> t;

  int8ToReg: word 8 -> t;
  int16ToReg: word 16 -> t;
  int32ToReg: word 32 -> t;
  int64ToReg: word 64 -> t;

  s32: t -> t;
  u32: t -> t;

  regToZ_signed: t -> Z;
  regToZ_unsigned: t -> Z;

  sll: t -> Z -> t;
  srl: t -> Z -> t;
  sra: t -> Z -> t;

  ltu: t -> t -> bool;
  divu: t -> t -> t;
  remu: t -> t -> t;

  maxSigned: t;
  maxUnsigned: t;
  minSigned: t;

  regToShamt5: t -> Z;
  regToShamt: t -> Z;

  highBits: Z -> t;
}.


Notation "a <|> b" := (or a b)  (at level 50, left associativity) : alu_scope.
Notation "a <&> b" := (and a b) (at level 40, left associativity) : alu_scope.
Notation "a + b"   := (add a b) (at level 50, left associativity) : alu_scope.
Notation "a - b"   := (sub a b) (at level 50, left associativity) : alu_scope.
Notation "a * b"   := (mul a b) (at level 40, left associativity) : alu_scope.

Notation "a /= b" := (negb (signed_eqb a b))        (at level 38, no associativity) : alu_scope.
Notation "a == b" := (signed_eqb a b)               (at level 38, no associativity) : alu_scope.
Notation "a < b"  := (signed_less_than a b)         (at level 70, no associativity) : alu_scope.
Notation "a >= b" := (negb (signed_less_than a b))  (at level 70, no associativity) : alu_scope.
Notation "'when' a b" := (if a then b else Return tt)
  (at level 60, a at level 0, b at level 0) : alu_scope.


Section Constants.

  Context {t: Set}.
  Context {MW: MachineWidth t}.

  Local Open Scope alu_scope.

  Definition two: t := one + one.

  Definition four: t := two + two.

  Definition eight: t := four + four.

  Definition negate(x: t): t := zero - x.
             
  Definition minusone: t := negate one.

  Definition lnot(x: t): t := xor x maxUnsigned.

End Constants.

Definition machineIntToShamt: MachineInt -> Z := id.

(* Note: If you think that wlt_dec and wslt_dec are too expensive to reduce with
   cbv, you can use wltb and wsltb instead, but it turned out that this
   was not the problem. *)

(* Redefine shifts so that they do not use eq_rect, which matches on add_comm,
   which is an opaque proof, which makes cbv blow up *)
Notation wlshift  := (@wlshift'  _).
Notation wrshift  := (@wrshift'  _).
Notation wrshifta := (@wrshifta' _).

Instance MachineWidth32: MachineWidth (word 32) := {|
  zero := $0;
  one := $1;
  add := @wplus 32;
  sub := @wminus 32;
  mul := @wmult 32;
  div x y := @ZToWord 32 (Z.div (wordToZ x) (wordToZ y));
  rem x y := @ZToWord 32 (Z.modulo (wordToZ x) (wordToZ y));
  signed_less_than a b := if wslt_dec a b then true else false;
  signed_eqb := @weqb 32;
  xor := @wxor 32;
  or := @wor 32;
  and := @wand 32;
  fromImm := ZToWord 32;
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
|}.

(* bbv thinks this should be opaque, but we need it transparent to make sure it reduces *)
Global Transparent wlt_dec.

(* Test that all operations reduce under cbv.
   If something prints a huge term with unreduced matches in it, running small examples
   inside Coq will not work! *)
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

Instance MachineWidth64: MachineWidth (word 64) := {|
  zero := $0;
  one := $1;
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
|}.

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

Instance MachineWidthInst{B: RiscvBitWidths}: MachineWidth (word wXLEN).
  unfold wXLEN.
  destruct bitwidth; [exact MachineWidth32 | exact MachineWidth64].
Defined.

Section Alu_Defs.
  Context {Bw: RiscvBitWidths}.
  
  Local Ltac prove_alu_def :=
    intros; clear; unfold wXLEN in *; unfold MachineWidthInst;
    destruct bitwidth; [unfold MachineWidth32 | unfold MachineWidth64]; reflexivity.

  Lemma fromImm_def: forall (a: Z),
      fromImm a = ZToWord wXLEN a.
  Proof. unfold fromImm. prove_alu_def. Qed.

  Lemma zero_def:
      zero = $0.
  Proof. unfold zero. prove_alu_def. Qed.
  
  Lemma one_def:
      one = $1.
  Proof. unfold one. prove_alu_def. Qed.
  
  Lemma add_def: forall (a b: word wXLEN),
      add a b = wplus a b.
  Proof. unfold add. prove_alu_def. Qed.
  
  Lemma sub_def: forall (a b: word wXLEN),
      sub a b = wminus a b.
  Proof. unfold sub. prove_alu_def. Qed.
  
  Lemma mul_def: forall (a b: word wXLEN),
      mul a b = wmult a b.
  Proof. unfold mul. prove_alu_def. Qed.
  
  Lemma div_def: forall (a b: word wXLEN),
      div a b = ZToWord wXLEN (wordToZ a / wordToZ b).
  Proof. unfold div. prove_alu_def. Qed.

  Lemma rem_def: forall (a b: word wXLEN),
      rem a b = ZToWord wXLEN (wordToZ a mod wordToZ b).
  Proof. unfold rem. prove_alu_def. Qed.

  Lemma signed_less_than_def: forall (a b: word wXLEN),
      signed_less_than a b = if wslt_dec a b then true else false.
  Proof. unfold signed_less_than. prove_alu_def. Qed.
  
  Lemma signed_eqb_def: forall (a b: word wXLEN),
      signed_eqb a b = weqb a b.
  Proof. unfold signed_eqb. prove_alu_def. Qed.
  
  Lemma xor_def: forall (a b: word wXLEN),
      xor a b = wxor a b.
  Proof. unfold xor. prove_alu_def. Qed.
  
  Lemma or_def: forall (a b: word wXLEN),
      or a b = wor a b.
  Proof. unfold or. prove_alu_def. Qed.
  
  Lemma and_def: forall (a b: word wXLEN),
      and a b = wand a b.
  Proof. unfold and. prove_alu_def. Qed.
  
  Lemma sll_def: forall (a: word wXLEN) (b: Z),
      sll a b = wlshift a (Z.to_nat b).
  Proof. unfold sll. prove_alu_def. Qed.
  
  Lemma srl_def: forall (a: word wXLEN) (b: Z),
      srl a b = wrshift a (Z.to_nat b).
  Proof. unfold srl. prove_alu_def. Qed.
  
  Lemma sra_def: forall (a: word wXLEN) (b: Z),
      sra a b = wrshift a (Z.to_nat b).
  Proof. unfold sra. prove_alu_def. Qed.
  
  Lemma ltu_def: forall (a b: word wXLEN),
      ltu a b = if wlt_dec a b then true else false.
  Proof. unfold ltu. prove_alu_def. Qed.
  
  Lemma divu_def: forall (a b: word wXLEN),
      divu a b = wdiv a b.
  Proof. unfold divu. prove_alu_def. Qed.

  Lemma remu_def: forall (a b: word wXLEN),
      remu a b = wmod a b.
  Proof. unfold remu. prove_alu_def. Qed.

End Alu_Defs.

Hint Rewrite
  @fromImm_def
  @zero_def
  @one_def
  @add_def
  @sub_def
  @mul_def
  @div_def
  @rem_def
  @signed_less_than_def
  @signed_eqb_def
  @xor_def
  @or_def
  @and_def
  @sll_def
  @srl_def
  @sra_def
  @ltu_def
  @divu_def
  @remu_def
: alu_defs.
