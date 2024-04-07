Require Import Coq.ZArith.ZArith.
Require Import Coq.Program.Tactics.
Require Import Coq.Bool.Bool.
Require Import riscv.Spec.Decode.
Require Import riscv.Utility.Utility.
Require Import riscv.Utility.Encode.
Require Import coqutil.Decidable.


#[export] Instance verify_Invalid_BoolSpec i : BoolSpec (verify_Invalid i) (~verify_Invalid i) false.
Proof. cbv; constructor; trivial. Defined.
#[export] Hint Opaque verify_Invalid : typeclass_instances.

#[export] Instance verify_R_BoolSpec opcode rd rs1 rs2 funct3 funct7 : BoolSpec (verify_R opcode rd rs1 rs2 funct3 funct7) _ _ := _.
#[export] Hint Opaque verify_R : typeclass_instances.

#[export] Instance verify_R_atomic_BoolSpec opcode rd rs1 rs2 funct3 aqrl funct5 : BoolSpec (verify_R_atomic opcode rd rs1 rs2 funct3 aqrl funct5) _ _ := _.
#[export] Hint Opaque verify_R_atomic : typeclass_instances.

#[export] Instance verify_I_BoolSpec opcode rd rs1 funct3 oimm12 : BoolSpec (verify_I opcode rd rs1 funct3 oimm12) _ _ := _.
#[export] Hint Opaque verify_I : typeclass_instances.

#[export] Instance verify_I_shift_57_BoolSpec opcode rd rs1 shamt5 funct3 funct7 : BoolSpec (verify_I_shift_57 opcode rd rs1 shamt5 funct3 funct7) _ _ := _.
#[export] Hint Opaque verify_I_shift_57 : typeclass_instances.

#[export] Instance verify_I_shift_66_BoolSpec bitwidth opcode rd rs1 shamt6 funct3 funct6 : BoolSpec (verify_I_shift_66 bitwidth opcode rd rs1 shamt6 funct3 funct6) _ _ := _.
#[export] Hint Opaque verify_I_shift_66 : typeclass_instances.

#[export] Instance verify_I_system_BoolSpec opcode rd rs1 funct3 funct12 : BoolSpec (verify_I_system opcode rd rs1 funct3 funct12) _ _ := _.
#[export] Hint Opaque verify_I_system : typeclass_instances.

#[export] Instance verify_S_BoolSpec opcode rs1 rs2 funct3 simm12 : BoolSpec (verify_S opcode rs1 rs2 funct3 simm12) _ _ := _.
#[export] Hint Opaque verify_S : typeclass_instances.

#[export] Instance verify_SB_BoolSpec opcode rs1 rs2 funct3 sbimm12 : BoolSpec (verify_SB opcode rs1 rs2 funct3 sbimm12) _ _ := _.
#[export] Hint Opaque verify_SB : typeclass_instances.

#[export] Instance verify_U_BoolSpec opcode rd imm20 : BoolSpec (verify_U opcode rd imm20) _ _ := _.
#[export] Hint Opaque verify_U : typeclass_instances.

#[export] Instance verify_UJ_BoolSpec opcode rd jimm20 : BoolSpec (verify_UJ opcode rd jimm20) _ _ := _.
#[export] Hint Opaque verify_UJ : typeclass_instances.

#[export] Instance verify_Fence_BoolSpec opcode rd rs1 funct3 prd scc msb4 : BoolSpec (verify_Fence opcode rd rs1 funct3 prd scc msb4) _ _ := _.
#[export] Hint Opaque verify_Fence : typeclass_instances.

#[export] Instance verify_FenceI_BoolSpec opcode rd rs1 funct3 imm12 : BoolSpec (verify_FenceI opcode rd rs1 funct3 imm12) _ _ := _.
#[export] Hint Opaque verify_FenceI : typeclass_instances.

Local Ltac destruct_in_all_evars v :=
  let ev := match goal with
            | [ |- context[?ev] ] => let __ := match goal with _ => is_evar ev end in
                                     ev
            end in
  let H := fresh in
  set (H := ev);
  instantiate (1:=ltac:(destruct v)) in (value of H);
  try destruct_in_all_evars v;
  subst H.
Local Ltac destruct_if_var i := try (is_var i; try destruct_in_all_evars i; destruct i).

Local Hint Extern 1 (BoolSpec (respects_bounds _ ?i) _ _)
      => destruct_if_var i; cbv [apply_InstructionMapper
                                   respects_bounds
                                   Verifier
                                   map_Invalid
                                   map_R
                                   map_R_atomic
                                   map_I
                                   map_I_shift_57
                                   map_I_shift_66
                                   map_I_system
                                   map_S
                                   map_SB
                                   map_U
                                   map_UJ
                                   map_Fence
                                   map_FenceI]
  : typeclass_instances.
Local Hint Extern 1 (BoolSpec (match ?i with _ => _ end) _ _)
      => destruct_if_var i; cbv beta iota : typeclass_instances.

#[export] Instance respects_bounds_BoolSpec bitwidth i : BoolSpec (respects_bounds bitwidth i) _ _ := _.
#[export] Hint Opaque respects_bounds : typeclass_instances.

(* TODO: Move to coqutil? *)
#[local] Instance True_BoolSpec : BoolSpec True False true := ltac:(constructor; trivial).
#[local] Instance False_BoolSpec : BoolSpec False True false := ltac:(constructor; trivial).

#[export] Instance InstructionSet_beq_spec : EqDecider InstructionSet_beq.
Proof.
  intros x y; generalize (@internal_InstructionSet_dec_bl x y), (@internal_InstructionSet_dec_lb x y).
  destruct InstructionSet_beq; constructor; auto; intro; subst; intuition congruence.
Defined.

Local Hint Extern 1 (BoolSpec (verify_iset ?inst _) _ _)
      => destruct_if_var inst; cbv [verify_iset]
  : typeclass_instances.

#[export] Instance verify_iset_BoolSpec inst iset : BoolSpec (verify_iset inst iset) _ _ := _.
#[export] Hint Opaque verify_iset : typeclass_instances.

#[export] Instance verify_BoolSpec inst iset : BoolSpec (verify inst iset) _ _ := _.
#[export] Hint Opaque verify : typeclass_instances.
