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
  
End Widths.
