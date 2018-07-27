Require Import Coq.ZArith.BinInt.
Require Import bbv.Word.
Require Import riscv.Utility.
Require Import riscv.MachineWidth32.
Require Import riscv.MachineWidth64.
Require Import riscv.util.BitWidths.


Instance MachineWidthInst{B: BitWidths}: MachineWidth (word wXLEN).
  unfold wXLEN.
  destruct bitwidth; [exact MachineWidth32 | exact MachineWidth64].
Defined.

Section Alu_Defs.
  Context {Bw: BitWidths}.
  
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

  (* derived defs: *)
  
  Lemma two_def: two = $2.
  Proof. unfold two. prove_alu_def. Qed.

  Lemma four_def: four = $4.
  Proof. unfold two. prove_alu_def. Qed.

  Lemma eight_def: eight = $8.
  Proof. unfold two. prove_alu_def. Qed.

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
  @two_def
  @four_def
  @eight_def
: alu_defs.
