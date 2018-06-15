Require Import Coq.omega.Omega.
Require Import bbv.NatLib.

Inductive BitWidth := BW32 | BW64.

Class BitWidths := bitwidth: BitWidth.

Section Widths.

  Context {B: BitWidths}.

  Definition wXLEN: nat :=
    match bitwidth with
    | BW32 => 32
    | BW64 => 64
    end.

  Definition log2wXLEN: nat :=
    match bitwidth with
    | BW32 => 5
    | BW64 => 6
    end.

  Definition wXLEN_in_bytes: nat :=
    match bitwidth with
    | BW32 => 4
    | BW64 => 8
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
