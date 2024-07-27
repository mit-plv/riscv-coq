From Coq Require Import ZArith.
Require Import riscv.Spec.Decode.
Require Import riscv.Utility.Encode.
Require Import riscv.Utility.Utility.

(* same verification functions as in Encode, but computable: *)

From Coq Require Import Derive.

Lemma andb_spec: forall P Q p q,
    Bool.reflect P p ->
    Bool.reflect Q q ->
    Bool.reflect (P /\ Q) (p && q).
Proof.
  intros. destruct H; destruct H0; constructor; intuition idtac.
Qed.

Lemma orb_spec: forall P Q p q,
    Bool.reflect P p ->
    Bool.reflect Q q ->
    Bool.reflect (P \/ Q) (p || q).
Proof.
  intros. destruct H; destruct H0; constructor; intuition idtac.
Qed.

Lemma negb_spec: forall P p,
    Bool.reflect P p ->
    Bool.reflect (~ P) (negb p).
Proof.
  intros. destruct H; constructor; intuition idtac.
Qed.

Lemma true_spec: Bool.reflect True true. Proof. constructor. constructor. Qed.

Lemma false_spec: Bool.reflect False false. Proof. constructor. auto. Qed.

Local Ltac t :=
  intros;
  repeat match goal with
    | x := _ |- _ => subst x
    end;
  repeat first
    [ eapply andb_spec
    | eapply orb_spec
    | eapply Z.leb_spec0
    | eapply Z.ltb_spec0
    | eapply Z.eqb_spec
    | eapply true_spec
    | eapply false_spec ].

Derive bverify_Invalid SuchThat
  (forall i: Z, Bool.reflect (verify_Invalid i) (bverify_Invalid i))
As bverify_Invalid_spec.
  subst bverify_Invalid.
  intros. unfold verify_Invalid. eapply Bool.ReflectF. auto.
Defined.

Derive bverify_R SuchThat
  (forall (opcode: MachineInt)(rd rs1 rs2: Register)(funct3 funct7: MachineInt),
      Bool.reflect (verify_R opcode rd rs1 rs2 funct3 funct7)
                  (bverify_R opcode rd rs1 rs2 funct3 funct7))
As bverify_R_spec. t. Defined.

Derive bverify_R_atomic SuchThat
  (forall (opcode: MachineInt)(rd rs1 rs2: Register)(funct3 aqrl funct5: MachineInt),
      Bool.reflect (verify_R_atomic opcode rd rs1 rs2 funct3 aqrl funct5)
                  (bverify_R_atomic opcode rd rs1 rs2 funct3 aqrl funct5))
As bverify_R_atomic_spec. t. Defined.

Derive bverify_I SuchThat
  (forall (opcode: MachineInt)(rd rs1: Register)(funct3: MachineInt)(oimm12: Z),
      Bool.reflect (verify_I opcode rd rs1 funct3 oimm12)
                  (bverify_I opcode rd rs1 funct3 oimm12))
As bverify_I_spec. t. Defined.

Derive bverify_I_shift_57 SuchThat
  (forall (opcode: MachineInt)(rd rs1: Register)(shamt5 funct3 funct7: MachineInt),
      Bool.reflect (verify_I_shift_57 opcode rd rs1 shamt5 funct3 funct7)
                  (bverify_I_shift_57 opcode rd rs1 shamt5 funct3 funct7))
As bverify_I_shift_57_spec. t. Defined.

Derive bverify_I_shift_66 SuchThat
  (forall (bitwidth: Z)(opcode: MachineInt)(rd rs1: Register)(shamt6 funct3 funct6: MachineInt),
      Bool.reflect (verify_I_shift_66 bitwidth opcode rd rs1 shamt6 funct3 funct6)
                  (bverify_I_shift_66 bitwidth opcode rd rs1 shamt6 funct3 funct6))
As bverify_I_shift_66_spec. t. Defined.

Derive bverify_I_system SuchThat
  (forall (opcode: MachineInt)(rd rs1: Register)(funct3 funct12: MachineInt),
      Bool.reflect (verify_I_system opcode rd rs1 funct3 funct12)
                  (bverify_I_system opcode rd rs1 funct3 funct12))
As bverify_I_system_spec. t. Defined.

Derive bverify_S SuchThat
  (forall (opcode: MachineInt)(rs1 rs2: Register)(funct3: MachineInt)(simm12: Z),
      Bool.reflect (verify_S opcode rs1 rs2 funct3 simm12)
                  (bverify_S opcode rs1 rs2 funct3 simm12))
As bverify_S_spec. t. Defined.

Derive bverify_SB SuchThat
  (forall (opcode: MachineInt)(rs1 rs2: Register)(funct3: MachineInt)(sbimm12: Z),
      Bool.reflect (verify_SB opcode rs1 rs2 funct3 sbimm12)
                  (bverify_SB opcode rs1 rs2 funct3 sbimm12))
As bverify_SB_spec. t. Defined.

Derive bverify_U SuchThat
  (forall (opcode: MachineInt)(rd: Register)(imm20: Z),
      Bool.reflect (verify_U opcode rd imm20)
                  (bverify_U opcode rd imm20))
As bverify_U_spec. t. Defined.

Derive bverify_UJ SuchThat
  (forall (opcode: MachineInt)(rd: Register)(jimm20: Z),
      Bool.reflect (verify_UJ opcode rd jimm20)
                  (bverify_UJ opcode rd jimm20))
As bverify_UJ_spec. t. Defined.

Derive bverify_Fence SuchThat
  (forall (opcode: MachineInt)(rd rs1: Register)(funct3 prd scc msb4: MachineInt),
      Bool.reflect (verify_Fence opcode rd rs1 funct3 prd scc msb4)
                  (bverify_Fence opcode rd rs1 funct3 prd scc msb4))
As bverify_Fence_spec. t. Defined.

Derive bverify_FenceI SuchThat
  (forall (opcode: MachineInt)(rd rs1: Register)(funct3 imm12: MachineInt),
      Bool.reflect (verify_FenceI opcode rd rs1 funct3 imm12)
                  (bverify_FenceI opcode rd rs1 funct3 imm12))
As bverify_FenceI_spec. t. Defined.

Definition bVerifier(bitwidth: Z): InstructionMapper bool := {|
  map_Invalid := bverify_Invalid;
  map_R := bverify_R;
  map_R_atomic := bverify_R_atomic;
  map_I := bverify_I;
  map_I_shift_57 := bverify_I_shift_57;
  map_I_shift_66 := bverify_I_shift_66 bitwidth;
  map_I_system := bverify_I_system;
  map_S := bverify_S;
  map_SB := bverify_SB;
  map_U := bverify_U;
  map_UJ := bverify_UJ;
  map_Fence := bverify_Fence;
  map_FenceI := bverify_FenceI;
|}.

Definition brespects_bounds(bitwidth: Z): Instruction -> bool :=
  apply_InstructionMapper (bVerifier bitwidth).

Lemma brespects_bounds_spec: forall bitwidth i,
    Bool.reflect (respects_bounds bitwidth i) (brespects_bounds bitwidth i).
Proof.
  intros. unfold respects_bounds, brespects_bounds.
  destruct i as [i | i | i | i | i | i | i | i | i | i ]; destruct i; simpl;
    eauto using bverify_Invalid_spec,
                bverify_R_spec,
                bverify_R_atomic_spec,
                bverify_I_spec,
                bverify_I_shift_57_spec,
                bverify_I_shift_66_spec,
                bverify_I_system_spec,
                bverify_S_spec,
                bverify_SB_spec,
                bverify_U_spec,
                bverify_UJ_spec,
                bverify_Fence_spec,
                bverify_FenceI_spec.
Qed.

Derive iset_eqb SuchThat
  (forall iset1 iset2: InstructionSet, Bool.reflect (iset1 = iset2) (iset_eqb iset1 iset2))
As iset_eqb_spec.
  Unshelve. 2: { intros iset1 iset2. destruct iset1; destruct iset2; shelve. }
  subst iset_eqb.
  destruct iset1; destruct iset2;
    first [ eapply Bool.ReflectT; reflexivity
          | eapply Bool.ReflectF; intro C; discriminate C ].
Defined.

Derive bverify_iset SuchThat
  (forall (inst: Instruction)(iset: InstructionSet),
      Bool.reflect (verify_iset inst iset) (bverify_iset inst iset))
As bverify_iset_spec.
  intros.
  let f := open_constr:(ltac:(intro inst'; destruct inst'; shelve):
                         Instruction -> InstructionSet -> bool) in
  unify bverify_iset f.
  destruct inst; simpl; t; eapply iset_eqb_spec.
Defined.

Definition bverify(inst: Instruction)(iset: InstructionSet): bool :=
  andb (brespects_bounds (bitwidth iset) inst) (bverify_iset inst iset).

Lemma bverify_spec: forall inst iset, Bool.reflect (verify inst iset) (bverify inst iset).
Proof. t; [eapply brespects_bounds_spec | eapply bverify_iset_spec]. Qed.

Definition valid_InvalidInstruction(instr: Decode.Instruction): Prop :=
  exists n, (0 <= n < 2 ^ 32)%Z /\ instr = InvalidInstruction n.

Definition bvalid_InvalidInstruction(instr: Decode.Instruction): bool :=
  match instr with
  | InvalidInstruction n => andb (0 <=? n)%Z (n <? 2 ^ 32)%Z
  | _ => false
  end.

Lemma bvalid_InvalidInstruction_spec: forall instr,
    Bool.reflect (valid_InvalidInstruction instr) (bvalid_InvalidInstruction instr).
Proof.
  destruct instr; cbn -[Z.pow]; cycle -1.
  1: destruct (0 <=? inst)%Z eqn: E1; [|simpl].
  1: destruct (inst <? 2 ^ 32)%Z eqn: E2; simpl.
  all: unfold valid_InvalidInstruction.
  { eapply Bool.ReflectT. eapply Z.leb_le in E1. eapply Z.ltb_lt in E2. eauto. }
  all: eapply Bool.ReflectF; intros (n & (A1 & A2) & B); inversion B; subst; clear B.
  { eapply Z.ltb_lt in A2. congruence. }
  { eapply Z.leb_le in A1. congruence. }
Qed.

Definition validInstruction(iset: InstructionSet)(i: Instruction): Prop :=
  verify i iset \/ valid_InvalidInstruction i.

Definition bvalidInstruction(iset: InstructionSet)(i: Instruction): bool :=
  orb (bverify i iset) (bvalid_InvalidInstruction i).

Lemma bvalidInstruction_spec: forall iset i,
    Bool.reflect (validInstruction iset i) (bvalidInstruction iset i).
Proof.
  intros. eapply orb_spec. 1: eapply bverify_spec. 1: eapply bvalid_InvalidInstruction_spec.
Qed.

Definition validInstructions(iset: InstructionSet): list Instruction -> Prop :=
  List.Forall (validInstruction iset).

Definition bvalidInstructions(iset: InstructionSet): list Instruction -> bool :=
  List.forallb (bvalidInstruction iset).

Lemma bvalidInstructions_spec: forall iset instrs,
    Bool.reflect (validInstructions iset instrs) (bvalidInstructions iset instrs).
Proof.
  intros. destruct (bvalidInstructions iset instrs) eqn: E;
    unfold bvalidInstructions, validInstructions in *.
  - eapply Bool.ReflectT.
    eapply List.Forall_forall.
    intros.
    eapply List.forallb_forall in E. 2: eassumption.
    eapply Bool.reflect_iff. 1: eapply bvalidInstruction_spec. assumption.
  - eapply Bool.ReflectF.
    intro C.
    pose proof (proj1 (List.Forall_forall _ _) C) as D.
    assert (forall i, List.In i instrs -> bvalidInstruction iset i = true) as F. {
      intros. eapply (proj1 (Bool.reflect_iff _ _ (bvalidInstruction_spec iset i))).
      eapply D. assumption.
    }
    eapply List.forallb_forall in F.
    congruence.
Qed.

Lemma bvalidInstructions_valid: forall iset instrs,
    bvalidInstructions iset instrs = true -> validInstructions iset instrs.
Proof. intros. eapply Bool.reflect_iff. 1: eapply bvalidInstructions_spec. assumption. Qed.
