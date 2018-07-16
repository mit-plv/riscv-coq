Require Import Coq.ZArith.BinInt.
Require Import Coq.setoid_ring.Ring_theory.
Require Import bbv.Word.
Require Import bbv.DepEqNat.
Require Import riscv.util.Monads.
Require Import riscv.util.BitWidths.
Require Export riscv.util.ZBitOps.


Local Open Scope Z_scope.

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

  (* bitwidth of type t: *)
  XLEN: Z;
  
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

  (* additional conversions: *)
  ZToReg: Z -> t;

  (* properties of operations: *)
  (* TODO list separately to make them more discoverable by "Search" *)
  regRing: @ring_theory t zero one add mul sub (fun x => sub zero x) (@eq t);
  ZToReg_morphism: @ring_morph t zero one add mul sub (fun x => sub zero x) (@eq t)
                               Z Z0 Z.one Z.add Z.mul Z.sub Z.opp Z.eqb ZToReg;
  (* not sure if needed or useful:
  regToNat: t -> nat;
  natToReg: nat -> t;
  natToReg_semimorph: @semi_morph t zero one add mul (@eq t)
                               nat O (S O) Nat.add Nat.mul Nat.eqb natToReg;
  regToNat_natToReg_idemp: forall n : nat, n < pow2 XLEN -> regToNat (natToReg n) = n;
  *)

  signed_eqb_spec: forall a b, signed_eqb a b = true <-> a = b;
  
  regToZ_signed_bounds: forall a, - 2 ^ (XLEN - 1) <= regToZ_signed a < 2 ^ (XLEN - 1);
  regToZ_unsigned_bounds: forall a, 0 <= regToZ_unsigned a < 2 ^ XLEN;

  add_def_signed: forall a b, add a b = ZToReg (regToZ_signed a + regToZ_signed b);
  sub_def_signed: forall a b, sub a b = ZToReg (regToZ_signed a - regToZ_signed b);
  mul_def_signed: forall a b, mul a b = ZToReg (regToZ_signed a * regToZ_signed b);
  (* TODO check corner cases of div and mod
  div_def: forall a b, div a b = ZToReg (regToZ_signed a / regToZ_signed b);
  rem_def: forall a b, rem a b = ZToReg (regToZ_signed a mod regToZ_signed b);
  *)

  regToZ_ZToReg_signed: forall n : Z,
      - 2 ^ (XLEN - 1) <= n < 2 ^ (XLEN - 1) ->
      regToZ_signed (ZToReg n) = n;

  ZToReg_regToZ_unsigned: forall a: t, ZToReg (regToZ_unsigned a) = a;
  ZToReg_regToZ_signed: forall a: t, ZToReg (regToZ_signed a) = a;

  XLEN_lbound: 8 <= XLEN;
}.


Section DerivedProperties.

  Context {t: Set}.
  Context {MW: MachineWidth t}.

  (* TODO rename signed_eqb to reg_eqb in Haskell *)
  Definition reg_eqb := signed_eqb.

  Definition XLEN_in_bytes: Z := XLEN / 8.

  Lemma reg_eqb_true: forall a b, reg_eqb a b = true <-> a = b.
  Proof.
    unfold reg_eqb. exact signed_eqb_spec.
  Qed.

  Lemma reg_eqb_false: forall a b, reg_eqb a b = false <-> a <> b.
  Proof.
    intros. split; intros.
    - intro. rewrite <- reg_eqb_true in H0. congruence.
    - destruct (reg_eqb a b) eqn: E; try congruence.
      exfalso. apply H. apply reg_eqb_true in E. assumption.
  Qed.
  
  Lemma add_def_unsigned: forall a b, add a b = ZToReg (regToZ_unsigned a + regToZ_unsigned b).
  Admitted.
  
  Lemma sub_def_unsigned: forall a b, sub a b = ZToReg (regToZ_unsigned a - regToZ_unsigned b).
  Admitted.
  
  Lemma mul_def_unsigned: forall a b, mul a b = ZToReg (regToZ_unsigned a * regToZ_unsigned b).
  Admitted.

  Lemma regToZ_ZToReg_unsigned: forall n : Z,
      (0 <= n < 2 ^ XLEN)%Z ->
      regToZ_unsigned (ZToReg n) = n.
  Admitted.
  
  
End DerivedProperties.  

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

(* bbv thinks this should be opaque, but we need it transparent to make sure it reduces *)
Global Transparent wlt_dec.
