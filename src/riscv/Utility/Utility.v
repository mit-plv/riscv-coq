Require Export Coq.ZArith.BinIntDef.
Require Import Coq.ZArith.ZArith.
Require Import Coq.setoid_ring.Ring_theory.
Require Export coqutil.Word.Interface.
Require Export coqutil.Word.Bitwidth.
Require Export coqutil.Byte.
Require Import coqutil.Datatypes.HList.
Require Import coqutil.sanity.
Require Export coqutil.Z.BitOps.

Global Unset Universe Minimization ToSet.

Local Open Scope Z_scope.

Notation bitSlice := coqutil.Z.BitOps.bitSlice.
Notation signExtend := coqutil.Z.BitOps.signExtend.

(* when we don't need any operators, we just use tuples of bytes: *)
Definition w8  := tuple byte 1.
Definition w16 := tuple byte 2.
Definition w32 := tuple byte 4.
Definition w64 := tuple byte 8.

(* Meaning of MachineInt: an integer big enough to hold an integer of a RISCV machine,
   no matter whether it's a 32-bit or 64-bit machine. *)
Notation MachineInt := Z (only parsing).

(* t is a parameter rather than a field for Haskell compatibility *)
Class MachineWidth(t: Type) := {

  (* arithmetic operations (inherited from wegral in Haskell) *)
  add: t -> t -> t;
  sub: t -> t -> t;
  mul: t -> t -> t;
  div: t -> t -> t;
  rem: t -> t -> t;

  negate: t -> t;

  (* comparison operators *)
  reg_eqb: t -> t -> bool;
  signed_less_than: t -> t -> bool;
  ltu: t -> t -> bool;

  (* logical operations (inherited from Bits in Haskell) *)
  xor: t -> t -> t;
  or: t -> t -> t;
  and: t -> t -> t;

  (* bitwidth of type t: *)
  XLEN: Z;

  (* operations also defined in MachineWidth in Haskell: *)

  regToInt8: t -> w8;
  regToInt16: t -> w16;
  regToInt32: t -> w32;
  regToInt64: t -> w64;

  uInt8ToReg: w8 -> t;
  uInt16ToReg: w16 -> t;
  uInt32ToReg: w32 -> t;
  uInt64ToReg: w64 -> t;

  int8ToReg: w8 -> t;
  int16ToReg: w16 -> t;
  int32ToReg: w32 -> t;
  int64ToReg: w64 -> t;

  s32: t -> t;
  u32: t -> t;

  regToZ_signed: t -> Z;
  regToZ_unsigned: t -> Z;

  sll: t -> Z -> t;
  srl: t -> Z -> t;
  sra: t -> Z -> t;

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
}.

Notation fromImm := (@ZToReg _ _) (only parsing).

Section Derived.

  Context {t: Type}.
  Context {MW: MachineWidth t}.

  Definition XLEN_in_bytes: Z := XLEN / 8.

  Definition lnot(x: t): t := xor x maxUnsigned.

End Derived.

Declare Scope alu_scope.

Notation "a <|> b" := (or a b)  (at level 50, left associativity) : alu_scope.
Notation "a <&> b" := (and a b) (at level 40, left associativity) : alu_scope.
Notation "a + b"   := (add a b) (at level 50, left associativity) : alu_scope.
Notation "a - b"   := (sub a b) (at level 50, left associativity) : alu_scope.
Notation "a * b"   := (mul a b) (at level 40, left associativity) : alu_scope.

Notation "a /= b" := (negb (reg_eqb a b))        (at level 38, no associativity) : alu_scope.
Notation "a == b" := (reg_eqb a b)               (at level 38, no associativity) : alu_scope.
Notation "a < b"  := (signed_less_than a b)         (at level 70, no associativity) : alu_scope.
Notation "a >= b" := (negb (signed_less_than a b))  (at level 70, no associativity) : alu_scope.

Definition machineIntToShamt: MachineInt -> Z := id.
