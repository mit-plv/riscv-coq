Require Import Coq.ZArith.ZArith.
Require Import coqutil.Map.Interface.
Require Import coqutil.Map.SortedList.
Require Import coqutil.Z.Lia.
Require Import riscv.Utility.Utility.
Require Import riscv.Spec.CSRField.
Local Open Scope Z_scope.

Definition CSRField_to_Z(f: CSRField): Z :=
  match f with
  | MXL => 0
  | Extensions => 1
  | SXL => 2
  | UXL => 3
  | TSR => 4
  | TW => 5
  | TVM => 6
  | MXR => 7
  | SUM => 8
  | MPRV => 9
  | XS => 10
  | FS => 11
  | MPP => 12
  | SPP => 13
  | MPIE => 14
  | SPIE => 15
  | UPIE => 16
  | MIE => 17
  | SIE => 18
  | UIE => 19
  | SD => 20
  | MTVecBase => 21
  | MTVecMode => 22
  | MEDeleg => 23
  | MIDeleg => 24
  | MEIP => 25
  | SEIP => 26
  | UEIP => 27
  | MTIP => 28
  | STIP => 29
  | UTIP => 30
  | MSIP => 31
  | SSIP => 32
  | USIP => 33
  | MEIE => 34
  | SEIE => 35
  | UEIE => 36
  | MTIE => 37
  | STIE => 38
  | UTIE => 39
  | MSIE => 40
  | SSIE => 41
  | USIE => 42
  | MCycle => 43
  | MInstRet => 44
  | MHPM => 45
  | MIR => 46
  | MTM => 47
  | MCY => 48
  | MScratch => 49
  | MEPC => 50
  | MCauseInterrupt => 51
  | MCauseCode => 52
  | MTVal => 53
  | STVecBase => 54
  | STVecMode => 55
  | SHPM => 56
  | SIR => 57
  | STM => 58
  | SCY => 59
  | SScratch => 60
  | SEPC => 61
  | SCauseInterrupt => 62
  | SCauseCode => 63
  | STVal => 64
  | MODE => 65
  | ASID => 66
  | PPN => 67
  | FFlags => 68
  | FRM => 69
  end.

Lemma CSRField_to_Z_inj: forall f1 f2,
    CSRField_to_Z f1 = CSRField_to_Z f2 ->
    f1 = f2.
Proof. intros. destruct f1; destruct f2; simpl in *; congruence. Qed.

Definition CSRField_ltb(f1 f2: CSRField): bool := Z.ltb (CSRField_to_Z f1) (CSRField_to_Z f2).

#[global] Instance CSRField_ltb_strictorder: SortedList.parameters.strict_order CSRField_ltb.
Proof.
  constructor; unfold CSRField_ltb; intros.
  - apply Z.ltb_irrefl.
  - rewrite ?Z.ltb_lt in *. blia.
  - apply CSRField_to_Z_inj.
    rewrite Z.ltb_ge in *.
    blia.
Qed.

#[global] Instance CSRFile_map_params: SortedList.parameters := {|
  parameters.key := CSRField;
  parameters.value := MachineInt;
  parameters.ltb := CSRField_ltb;
|}.

#[global] Instance CSRFile: map.map CSRField MachineInt :=
  SortedList.map CSRFile_map_params CSRField_ltb_strictorder.

#[global] Instance CSRFile_ok: map.ok CSRFile.
Proof. apply (@SortedList.map_ok CSRFile_map_params CSRField_ltb_strictorder). Qed.
