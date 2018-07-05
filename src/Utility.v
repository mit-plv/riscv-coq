Require Import Coq.ZArith.BinInt.
Require Import Coq.setoid_ring.Ring_theory.
Require Import bbv.Word.
Require Import bbv.DepEqNat.
Require Import riscv.util.Monads.
Require Import riscv.util.BitWidths.
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

  (* bitwidth of type t: *)
  XLEN: nat;
  
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
  regToNat: t -> nat;
  natToReg: nat -> t;
  ZToReg: Z -> t;

  (* properties of operations: *)
  regRing: @ring_theory t zero one add mul sub (fun x => sub zero x) (@eq t);
  (* not sure if needed or useful:
  natToReg_semimorph: @semi_morph t zero one add mul (@eq t)
                               nat O (S O) Nat.add Nat.mul Nat.eqb natToReg;
  ZToReg_morphism: @ring_morph t zero one add mul sub (fun x => sub zero x) (@eq t)
                               Z Z0 Z.one Z.add Z.mul Z.sub Z.opp Z.eqb ZToReg;
  *)
  regToNat_natToReg_idemp: forall n : nat, n < pow2 XLEN -> regToNat (natToReg n) = n;
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

(* bbv thinks this should be opaque, but we need it transparent to make sure it reduces *)
Global Transparent wlt_dec.
