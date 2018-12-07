Require Import Coq.ZArith.ZArith.
Require Import Coq.setoid_ring.Ring_theory.
Require Export coqutil.Word.Interface.
Require Import riscv.util.Monads.
Require Export riscv.util.ZBitOps.


Local Open Scope Z_scope.

(* Meaning of MachineInt: an integer big enough to hold an integer of a RISCV machine,
   no matter whether it's a 32-bit or 64-bit machine. *)
Definition MachineInt := Z.

Class MachineWidth(t: Set) := {
  w8  : Set;
  w16 : Set;
  w32 : Set;
  w64 : Set;

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

  (* properties of operations: *)
  (* TODO list separately to make them more discoverable by "Search" *)
  regRing: @ring_theory t (ZToReg 0) (ZToReg 1) add mul sub negate (@eq t);
  ZToReg_morphism: @ring_morph t (ZToReg 0) (ZToReg 1) add mul sub negate (@eq t)
                               Z 0 1 Z.add Z.mul Z.sub Z.opp Z.eqb ZToReg;

  reg_eqb_spec: forall a b, reg_eqb a b = true <-> a = b;

  regToZ_signed_bounds: forall a, - 2 ^ (XLEN - 1) <= regToZ_signed a < 2 ^ (XLEN - 1);
  regToZ_unsigned_bounds: forall a, 0 <= regToZ_unsigned a < 2 ^ XLEN;

  add_def_signed: forall a b, add a b = ZToReg (regToZ_signed a + regToZ_signed b);
  sub_def_signed: forall a b, sub a b = ZToReg (regToZ_signed a - regToZ_signed b);
  mul_def_signed: forall a b, mul a b = ZToReg (regToZ_signed a * regToZ_signed b);

  regToZ_ZToReg_signed: forall n : Z,
      - 2 ^ (XLEN - 1) <= n < 2 ^ (XLEN - 1) ->
      regToZ_signed (ZToReg n) = n;
  regToZ_ZToReg_unsigned_mod: forall n : Z, regToZ_unsigned (ZToReg n) = n mod 2 ^ XLEN;

  ZToReg_regToZ_unsigned: forall a: t, ZToReg (regToZ_unsigned a) = a;
  ZToReg_regToZ_signed: forall a: t, ZToReg (regToZ_signed a) = a;

  XLEN_lbound: 8 <= XLEN;

  (* Note: There are 3 ways to define div and mod:
     - truncate division (aka round towards zero, aka "T"), define mod as remainder wrt division
       Defined in Coq in Module ZDivTrunc and available as Z.quot and Z.rem.
       That's also what RISC-V does, according to
       https://github.com/riscv/riscv-isa-manual/commit/3de73dedf7822bf35f0fa603e400c4f25c99b6d9
     - floor division (aka "F"), define mod as remainder wrt division
       Defined in Coq in Module ZDivFloor and available as Z.div and Z.modulo.
     - Euclidian division, where the remainder never is negative (aka "E"):
       forall a b, b<>0 -> exists r q, a = b*q+r /\ 0 < r < |b|
       Defined in Coq in Module ZDivEucl.
     Note: The corner cases (division by 0, overflow) are handled in ExecuteM.
  *)
  div_def : forall a b, div  a b = ZToReg (Z.quot (regToZ_signed   a) (regToZ_signed   b));
  rem_def : forall a b, rem  a b = ZToReg (Z.rem  (regToZ_signed   a) (regToZ_signed   b));
  divu_def: forall a b, divu a b = ZToReg (Z.quot (regToZ_unsigned a) (regToZ_unsigned b));
  remu_def: forall a b, remu a b = ZToReg (Z.rem  (regToZ_unsigned a) (regToZ_unsigned b));
}.

Notation fromImm := (@ZToReg _ _) (only parsing).

Section Derived.

  Context {t: Set}.
  Context {MW: MachineWidth t}.

  Definition XLEN_in_bytes: Z := XLEN / 8.

  Definition lnot(x: t): t := xor x maxUnsigned.

  Lemma reg_eqb_true: forall a b, reg_eqb a b = true -> a = b.
  Proof. apply reg_eqb_spec. Qed.

  Lemma reg_eqb_eq: forall a b, a = b -> reg_eqb a b = true.
  Proof. apply reg_eqb_spec. Qed.

  Lemma reg_eqb_false: forall a b, reg_eqb a b = false -> a <> b.
  Proof.
    intros. intro. rewrite reg_eqb_eq in H; congruence.
  Qed.

  Lemma reg_eqb_ne: forall a b, a <> b -> reg_eqb a b = false.
  Proof.
    intros. destruct (reg_eqb a b) eqn: E; try congruence.
    exfalso. apply H. apply reg_eqb_true in E. assumption.
  Qed.

  Lemma regToZ_ZToReg_unsigned: forall n : Z,
      0 <= n < 2 ^ XLEN ->
      regToZ_unsigned (ZToReg n) = n.
  Proof.
    intros.
    rewrite regToZ_ZToReg_unsigned_mod.
    apply Z.mod_small.
    assumption.
  Qed.

  Lemma add_def_unsigned: forall a b, add a b = ZToReg (regToZ_unsigned a + regToZ_unsigned b).
  Proof.
    intros.
    rewrite ZToReg_morphism.(morph_add). rewrite? ZToReg_regToZ_unsigned.
    reflexivity.
  Qed.

  Lemma sub_def_unsigned: forall a b, sub a b = ZToReg (regToZ_unsigned a - regToZ_unsigned b).
  Proof.
    intros.
    rewrite ZToReg_morphism.(morph_sub). rewrite? ZToReg_regToZ_unsigned.
    reflexivity.
  Qed.

  Lemma mul_def_unsigned: forall a b, mul a b = ZToReg (regToZ_unsigned a * regToZ_unsigned b).
  Proof.
    intros.
    rewrite ZToReg_morphism.(morph_mul). rewrite? ZToReg_regToZ_unsigned.
    reflexivity.
  Qed.

  Lemma ZToReg_inj_unsigned: forall a b,
      0 <= a < 2 ^ XLEN ->
      0 <= b < 2 ^ XLEN ->
      ZToReg a = ZToReg b ->
      a = b.
  Proof.
    intros.
    (* Check (ZToReg_morphism.(morph_eq)). the wrong way *)
  Abort.

  Lemma pow2_sz_4: 4 < 2 ^ XLEN.
  Proof.
    pose proof XLEN_lbound.
    change 4 with (2 ^ 2).
    apply Z.pow_lt_mono_r; omega.
  Qed.

  Lemma regToZ_unsigned_eq: forall (a b: t), regToZ_unsigned a = regToZ_unsigned b -> a = b.
  Proof.
    intros.
    rewrite <- (ZToReg_regToZ_unsigned a).
    rewrite <- (ZToReg_regToZ_unsigned b).
    congruence.
  Qed.

  Lemma regToZ_unsigned_ne: forall (a b: t), regToZ_unsigned a <> regToZ_unsigned b -> a <> b.
  Proof.
    intros.
    intro C.
    subst b.
    apply H.
    reflexivity.
  Qed.

  Lemma ne_regToZ_unsigned: forall (a b: t),
      a <> b -> regToZ_unsigned a <> regToZ_unsigned b.
  Proof.
    intros.
    intro C.
    apply H.
    apply regToZ_unsigned_eq.
    assumption.
  Qed.

  Lemma regToZ_unsigned_one: regToZ_unsigned (ZToReg 1) = 1.
  Proof.
    intros.
    apply regToZ_ZToReg_unsigned. pose proof pow2_sz_4. omega.
  Qed.

  Lemma regToZ_unsigned_two: regToZ_unsigned (ZToReg 2) = 2.
  Proof.
    intros.
    apply regToZ_ZToReg_unsigned. pose proof pow2_sz_4. omega.
  Qed.

  Lemma regToZ_unsigned_four: regToZ_unsigned (ZToReg 4) = 4.
  Proof.
    intros.
    apply regToZ_ZToReg_unsigned. pose proof pow2_sz_4. omega.
  Qed.

End Derived.

Notation "a <|> b" := (or a b)  (at level 50, left associativity) : alu_scope.
Notation "a <&> b" := (and a b) (at level 40, left associativity) : alu_scope.
Notation "a + b"   := (add a b) (at level 50, left associativity) : alu_scope.
Notation "a - b"   := (sub a b) (at level 50, left associativity) : alu_scope.
Notation "a * b"   := (mul a b) (at level 40, left associativity) : alu_scope.

Notation "a /= b" := (negb (reg_eqb a b))        (at level 38, no associativity) : alu_scope.
Notation "a == b" := (reg_eqb a b)               (at level 38, no associativity) : alu_scope.
Notation "a < b"  := (signed_less_than a b)         (at level 70, no associativity) : alu_scope.
Notation "a >= b" := (negb (signed_less_than a b))  (at level 70, no associativity) : alu_scope.
Notation "'when' a b" := (if a then b else Return tt)
  (at level 60, a at level 0, b at level 0) : alu_scope.

Definition machineIntToShamt: MachineInt -> Z := id.
