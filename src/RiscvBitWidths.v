Require Import Coq.omega.Omega.
Require Import bbv.NatLib.

Inductive RiscvBitWidth := Bitwidth32 | Bitwidth64.

Class RiscvBitWidths := bitwidth: RiscvBitWidth.

Section Widths.

  Context {B: RiscvBitWidths}.

  Definition wXLEN: nat :=
    match bitwidth with
    | Bitwidth32 => 32
    | Bitwidth64 => 64
    end.

  Definition log2wXLEN: nat :=
    match bitwidth with
    | Bitwidth32 => 5
    | Bitwidth64 => 6
    end.

  Definition wXLEN_in_bytes: nat :=
    match bitwidth with
    | Bitwidth32 => 4
    | Bitwidth64 => 8
    end.

  Lemma pow2_wXLEN_4: 4 < pow2 wXLEN.
  Proof.
    unfold wXLEN, bitwidth. destruct B;
      do 2 rewrite pow2_S;
      change 4 with (2 * (2 * 1)) at 1;
      (repeat apply mult_lt_compat_l; [ | repeat constructor ..]);
      apply one_lt_pow2.
  Qed.  
  
End Widths.
