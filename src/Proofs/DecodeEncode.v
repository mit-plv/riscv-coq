Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List. Import ListNotations.
Require Import riscv.Spec.Decode.
Require Import riscv.Utility.Encode.
Require Import riscv.Utility.Utility.
Require Import riscv.Utility.Tactics.
Require Import riscv.Utility.div_mod_to_quot_rem.
Require Import riscv.Proofs.invert_encode_R.
Require Import riscv.Proofs.invert_encode_R_atomic.
Require Import riscv.Proofs.invert_encode_I.
Require Import riscv.Proofs.invert_encode_I_shift_57.
Require Import riscv.Proofs.invert_encode_I_shift_66.
Require Import riscv.Proofs.invert_encode_I_system.
Require Import riscv.Proofs.invert_encode_S.
Require Import riscv.Proofs.invert_encode_SB.
Require Import riscv.Proofs.invert_encode_U.
Require Import riscv.Proofs.invert_encode_UJ.
Require Import riscv.Proofs.invert_encode_Fence.

Local Open Scope bool_scope.
Local Open Scope Z_scope.


Ltac somega_pre :=
  rewrite? bitSlice_alt in * by omega; unfold bitSlice' in *;
  repeat (so fun hyporgoal => match hyporgoal with
  | context [signExtend ?l ?n] =>
      let E := fresh "E" in
      destruct (signExtend_alt' l n) as [[? [? E]] | [? [? E]]];
      [ omega | rewrite E in *; clear E .. ]
  end);
  rewrite? Z.shiftl_mul_pow2 in * by omega;
  repeat (so fun hyporgoal => match hyporgoal with
     | context [2 ^ ?x] => let r := eval cbv in (2 ^ x) in change (2 ^ x) with r in *
  end);
  div_mod_to_quot_rem;
  repeat match goal with
         | z: ?T |- _ => progress change T with Z in *
         end.

(* omega which understands bitSlice and shift *)
Ltac somega := somega_pre; omega.

Lemma invert_encode_InvalidInstruction: forall i,
  verify_Invalid i ->
  forall inst,
  encode_Invalid i = inst ->
  False.
Proof. intros. assumption. Qed.

Ltac cbn_encode := repeat (
  cbn [
    Z.eqb
    Pos.eqb andb
    opcode_SYSTEM
    opcode_STORE_FP
    opcode_STORE
    opcode_OP_IMM_32
    opcode_OP_IMM
    opcode_OP_FP
    opcode_OP_32
    opcode_OP
    opcode_NMSUB
    opcode_NMADD
    opcode_MSUB
    opcode_MISC_MEM
    opcode_MADD
    opcode_LUI
    opcode_LOAD_FP
    opcode_LOAD
    opcode_JALR
    opcode_JAL
    opcode_BRANCH
    opcode_AUIPC
    opcode_AMO
    funct7_XOR
    funct7_SUBW
    funct7_SUB
    funct7_SRLW
    funct7_SRLIW
    funct7_SRL
    funct7_SRAW
    funct7_SRAIW
    funct7_SRA
    funct7_SLTU
    funct7_SLT
    funct7_SLLW
    funct7_SLLIW
    funct7_SLL
    funct7_SFENCE_VMA
    funct7_REMW
    funct7_REMUW
    funct7_REMU
    funct7_REM
    funct7_OR
    funct7_MULW
    funct7_MULHU
    funct7_MULHSU
    funct7_MULH
    funct7_MUL
    funct7_FSUB_S
    funct7_FSQRT_S
    funct7_FSGNJ_S
    funct7_FMV_X_W
    funct7_FMV_W_X
    funct7_FMUL_S
    funct7_FMIN_S
    funct7_FEQ_S
    funct7_FDIV_S
    funct7_FCVT_W_S
    funct7_FCVT_S_W
    funct7_FCLASS_S
    funct7_FADD_S
    funct7_DIVW
    funct7_DIVUW
    funct7_DIVU
    funct7_DIV
    funct7_AND
    funct7_ADDW
    funct7_ADD
    funct6_SRLI
    funct6_SRAI
    funct6_SLLI
    funct5_SC
    funct5_LR
    funct5_AMOXOR
    funct5_AMOSWAP
    funct5_AMOOR
    funct5_AMOMINU
    funct5_AMOMIN
    funct5_AMOMAXU
    funct5_AMOMAX
    funct5_AMOAND
    funct5_AMOADD
    funct3_XORI
    funct3_XOR
    funct3_SW
    funct3_SUBW
    funct3_SUB
    funct3_SRLW
    funct3_SRLIW
    funct3_SRLI
    funct3_SRL
    funct3_SRAW
    funct3_SRAIW
    funct3_SRAI
    funct3_SRA
    funct3_SLTU
    funct3_SLTIU
    funct3_SLTI
    funct3_SLT
    funct3_SLLW
    funct3_SLLIW
    funct3_SLLI
    funct3_SLL
    funct3_SH
    funct3_SD
    funct3_SB
    funct3_REMW
    funct3_REMUW
    funct3_REMU
    funct3_REM
    funct3_PRIV
    funct3_ORI
    funct3_OR
    funct3_MULW
    funct3_MULHU
    funct3_MULHSU
    funct3_MULH
    funct3_MUL
    funct3_LWU
    funct3_LW
    funct3_LHU
    funct3_LH
    funct3_LD
    funct3_LBU
    funct3_LB
    funct3_FSW
    funct3_FSGNJ_S
    funct3_FSGNJX_S
    funct3_FSGNJN_S
    funct3_FMV_X_W
    funct3_FMIN_S
    funct3_FMAX_S
    funct3_FLW
    funct3_FLT_S
    funct3_FLE_S
    funct3_FEQ_S
    funct3_FENCE_I
    funct3_FENCE
    funct3_FCLASS_S
    funct3_DIVW
    funct3_DIVUW
    funct3_DIVU
    funct3_DIV
    funct3_CSRRWI
    funct3_CSRRW
    funct3_CSRRSI
    funct3_CSRRS
    funct3_CSRRCI
    funct3_CSRRC
    funct3_BNE
    funct3_BLTU
    funct3_BLT
    funct3_BGEU
    funct3_BGE
    funct3_BEQ
    funct3_ANDI
    funct3_AND
    funct3_AMOW
    funct3_AMOD
    funct3_ADDW
    funct3_ADDIW
    funct3_ADDI
    funct3_ADD
    funct2_FMADD_S
    funct12_WFI
    funct12_URET
    funct12_SRET
    funct12_MRET
    funct12_ECALL
    funct12_EBREAK
    isValidM64
    isValidM
    isValidI64
    isValidI
    isValidCSR
    isValidA64
    isValidA
    isValidF64
    isValidF
    supportsM
    supportsA
    supportsF
    bitwidth
    app
  ] in *;
  cbv [machineIntToShamt id] in *
).

Ltac invert_encode_old :=
  lazymatch goal with
  | Henc: encode_I _ _ _ _ _ = _ |- _ =>
    apply invert_encode_I in Henc
  | Henc: encode_Fence _ _ _ _ _ _ _ = _ |- _ =>
    apply invert_encode_Fence in Henc
  | Henc: encode_I_shift_66 _ _ _ _ _ _ = _, iset: InstructionSet |- _ =>
    apply (@invert_encode_I_shift_66 (bitwidth iset)) in Henc
  | Henc: encode_I_shift_57 _ _ _ _ _ _ = _ |- _ =>
    apply invert_encode_I_shift_57 in Henc
  | Henc: encode_R _ _ _ _ _ _ = _ |- _ =>
    apply invert_encode_R in Henc
  | Henc: encode_Invalid _ = _ |- _ =>
    apply invert_encode_InvalidInstruction in Henc; case Henc
  | Henc: encode_R_atomic _ _ _ _ _ _ _ = _ |- _ =>
    apply invert_encode_R_atomic in Henc
  | Henc: encode_I_system _ _ _ _ _ = _ |- _ =>
    apply invert_encode_I_system in Henc
  | Henc: encode_U _ _ _ = _ |- _ =>
    apply invert_encode_U in Henc
  | Henc: encode_UJ _ _ _ = _ |- _ =>
    apply invert_encode_UJ in Henc
  | Henc: encode_S _ _ _ _ _ = _ |- _ =>
    apply invert_encode_S in Henc
  | Henc: encode_SB _ _ _ _ _ = _ |- _ =>
    apply invert_encode_SB in Henc
  end;
  [|assumption..].

(* requires iset to be destructed *)
Ltac simpl_results_list :=
  cbv beta iota delta [
    isValidM64
    isValidM
    isValidI64
    isValidI
    isValidCSR
    isValidA64
    isValidA
    isValidF64
    isValidF
    supportsM
    supportsA
    supportsF
    bitwidth
  ] in *;
  change (32 =? 64) with false in *;
  change (64 =? 64) with true in *;
  change (true && false) with false in *;
  change (true && true) with true in *;
  change (false && false) with false in *;
  change (false && true) with false in *;
  cbv iota in *.

Set Printing Depth 1000000.

Ltac define_decoder :=
  let x := fresh "x" in let iset := fresh "iset" in let inst := fresh "inst" in
  intros iset inst;
  set (x := decode iset inst);
  revert x;
  cbv beta delta [decode];
  repeat match goal with
  | |- let x := let y := ?A in (@?B y) in ?C =>
    set (y := A); change (let x := (B y) in C); cbv beta
  end;
  intro x.


Definition mdecodeI': InstructionSet -> MachineInt -> InstructionI.
  define_decoder. exact decodeI.
Defined.
Definition mdecodeI: InstructionSet -> MachineInt -> InstructionI :=
  Eval cbv [decode mdecodeI'] in mdecodeI'.

Definition mdecodeM': InstructionSet -> MachineInt -> InstructionM.
  define_decoder. exact decodeM.
Defined.
Definition mdecodeM: InstructionSet -> MachineInt -> InstructionM :=
  Eval cbv [decode mdecodeM'] in mdecodeM'.

Definition mdecodeA': InstructionSet -> MachineInt -> InstructionA.
  define_decoder. exact decodeA.
Defined.
Definition mdecodeA: InstructionSet -> MachineInt -> InstructionA :=
  Eval cbv [decode mdecodeA'] in mdecodeA'.

Definition mdecodeF': InstructionSet -> MachineInt -> InstructionF.
  define_decoder. exact decodeF.
Defined.
Definition mdecodeF: InstructionSet -> MachineInt -> InstructionF :=
  Eval cbv [decode mdecodeF'] in mdecodeF'.

Definition mdecodeI64': InstructionSet -> MachineInt -> InstructionI64.
  define_decoder. exact decodeI64.
Defined.
Definition mdecodeI64: InstructionSet -> MachineInt -> InstructionI64 :=
  Eval cbv [decode mdecodeI64'] in mdecodeI64'.

Definition mdecodeM64': InstructionSet -> MachineInt -> InstructionM64.
  define_decoder. exact decodeM64.
Defined.
Definition mdecodeM64: InstructionSet -> MachineInt -> InstructionM64 :=
  Eval cbv [decode mdecodeM64'] in mdecodeM64'.

Definition mdecodeA64': InstructionSet -> MachineInt -> InstructionA64.
  define_decoder. exact decodeA64.
Defined.
Definition mdecodeA64: InstructionSet -> MachineInt -> InstructionA64 :=
  Eval cbv [decode mdecodeA64'] in mdecodeA64'.

Definition mdecodeF64': InstructionSet -> MachineInt -> InstructionF64.
  define_decoder. exact decodeF64.
Defined.
Definition mdecodeF64: InstructionSet -> MachineInt -> InstructionF64 :=
  Eval cbv [decode mdecodeF64'] in mdecodeF64'.

Definition mdecodeCSR': InstructionSet -> MachineInt -> InstructionCSR.
  define_decoder. exact decodeCSR.
Defined.
Definition mdecodeCSR: InstructionSet -> MachineInt -> InstructionCSR :=
  Eval cbv [decode mdecodeCSR'] in mdecodeCSR'.

Definition modular_decode': InstructionSet -> MachineInt -> Instruction.
  define_decoder.
  change decodeI with (mdecodeI iset inst) in *; clear decodeI.
  change decodeM with (mdecodeM iset inst) in *; clear decodeM.
  change decodeA with (mdecodeA iset inst) in *; clear decodeA.
  change decodeF with (mdecodeF iset inst) in *; clear decodeF.
  change decodeI64 with (mdecodeI64 iset inst) in *; clear decodeI64.
  change decodeM64 with (mdecodeM64 iset inst) in *; clear decodeM64.
  change decodeA64 with (mdecodeA64 iset inst) in *; clear decodeA64.
  change decodeF64 with (mdecodeF64 iset inst) in *; clear decodeF64.
  change decodeCSR with (mdecodeCSR iset inst) in *; clear decodeCSR.
  clear -x.
  (* almost copy-pastable *)
Abort.

Definition modular_decode(iset: InstructionSet)(inst: MachineInt): Instruction :=
  let resultCSR := if isValidCSR (mdecodeCSR iset inst)
                   then [CSRInstruction (mdecodeCSR iset inst)]
                   else [] in
  let resultF64 := if isValidF64 (mdecodeF64 iset inst)
                   then [F64Instruction (mdecodeF64 iset inst)]
                   else [] in
  let resultA64 := if isValidA64 (mdecodeA64 iset inst)
                   then [A64Instruction (mdecodeA64 iset inst)]
                   else [] in
  let resultM64 := if isValidM64 (mdecodeM64 iset inst)
                   then [M64Instruction (mdecodeM64 iset inst)]
                   else [] in
  let resultI64 := if isValidI64 (mdecodeI64 iset inst)
                   then [I64Instruction (mdecodeI64 iset inst)]
                   else [] in
  let resultF := if isValidF (mdecodeF iset inst) then [FInstruction (mdecodeF iset inst)] else [] in
  let resultA := if isValidA (mdecodeA iset inst) then [AInstruction (mdecodeA iset inst)] else [] in
  let resultM := if isValidM (mdecodeM iset inst) then [MInstruction (mdecodeM iset inst)] else [] in
  let resultI := if isValidI (mdecodeI iset inst) then [IInstruction (mdecodeI iset inst)] else [] in
  let results := resultI ++
                 (if supportsM iset then resultM else []) ++
                 (if supportsA iset then resultA else []) ++
                 (if supportsF iset then resultF else []) ++
                 (if bitwidth iset =? 64 then resultI64 else []) ++
                 (if (bitwidth iset =? 64) && supportsM iset then resultM64 else []) ++
                 (if (bitwidth iset =? 64) && supportsA iset then resultA64 else []) ++
                 (if (bitwidth iset =? 64) && supportsF iset then resultF64 else []) ++
                 resultCSR in
           if BinInt.Z.of_nat (length results) >? 1
           then InvalidInstruction inst
           else nth 0 results (InvalidInstruction inst).

Lemma decode_alt: forall iset inst, decode iset inst = modular_decode iset inst.
Proof.
  intros. reflexivity.
Qed.

Ltac invert_encode :=
  match goal with
  | E: _, V: _ |- _ => case (invert_encode_InvalidInstruction _ V _ E)
  | E: _, V: _ |- _ => pose proof (invert_encode_I V _ E); clear E V
  | E: _, V: _ |- _ => pose proof (invert_encode_Fence V _ E); clear E V
  | E: _, V: _ |- _ => pose proof (invert_encode_I_shift_66 V _ E); clear E V
  | E: _, V: _ |- _ => pose proof (invert_encode_I_shift_57 V _ E); clear E V
  | E: _, V: _ |- _ => pose proof (invert_encode_R V _ E); clear E V
  | E: _, V: _ |- _ => pose proof (invert_encode_R_atomic V _ E); clear E V
  | E: _, V: _ |- _ => pose proof (invert_encode_I_system V _ E); clear E V
  | E: _, V: _ |- _ => pose proof (invert_encode_U V _ E); clear E V
  | E: _, V: _ |- _ => pose proof (invert_encode_UJ V _ E); clear E V
  | E: _, V: _ |- _ => pose proof (invert_encode_S V _ E); clear E V
  | E: _, V: _ |- _ => pose proof (invert_encode_SB V _ E); clear E V
  end.

Ltac prove_decode_encode :=
  let iset := fresh "iset" in let inst := fresh "inst" in let V := fresh "V" in
  intros iset inst V; unfold verify in V; destruct V;
  unfold verify_iset in *;
  let Henc := fresh "Henc" in
  match goal with
  | |- ?D ?I (encode ?x) = _ =>
    remember (encode x) as encoded eqn:Henc; symmetry in Henc
  end;
  cbv [encode] in Henc;
  cbv [
      Encoder
        Verifier
        apply_InstructionMapper
        map_Fence
        map_I
        map_I_shift_57
        map_I_shift_66
        map_I_system
        map_Invalid
        map_R
        map_R_atomic
        map_S
        map_SB
        map_U
        map_UJ
    ] in Henc;
  match goal with
  | |- ?D ?I _ = _ => cbv [D]
  end;
  (* will split from 1 goal into ~8 goals *)
  destruct iset;
  try abstract (
    (* multiplies number of goals by up to 80 *)
    destruct inst;
    invert_encode;
    match goal with
    | Henc: _ /\ _ |- _ =>
      repeat match type of Henc with
             |  _ /\ _ => let H := fresh "H" in destruct Henc as [H Henc]; rewrite <-?H in *
             end;
        rewrite <-?Henc in *
    end;
    repeat match goal with
    | |- (if ?b then ?x else ?y) = ?z => change (y = z)
    end;
    match goal with
    | |- (if ?b then ?x else ?y) = ?z => change (x = z); reflexivity
    | |- (if ?b then ?x else ?y) = ?x => replace b with true; [reflexivity|]
    end;
    (* cases where bitSlice in goal and hyps do not match *)
    repeat match goal with
           | |- context [?a =?  _] => unfold a
           | |- context [_  =? ?a] => unfold a
           end;
     repeat match goal with
            | |- ?x = ?x => exact_no_check (eq_refl x)
            | |- context [?x =? ?y] =>
              let H := fresh "H" in
              destruct (x =? y) eqn:H;
                apply Z.eqb_eq in H || apply Z.eqb_neq in H
            | _ => progress cbn in *
            end;
     try (intuition discriminate);
     try solve [ exfalso;
                 try (match goal with H: _ <> _ |- _ => apply H; clear H end);
                 somega ]).

Lemma mdecodeI_encode: forall (inst: InstructionI) (iset: InstructionSet),
    verify (IInstruction inst) iset ->
    mdecodeI iset (encode (IInstruction inst)) = inst.
Proof.
  prove_decode_encode.
Qed.

Lemma mdecodeM_encode: forall (inst: InstructionM) (iset: InstructionSet),
    verify (MInstruction inst) iset ->
    mdecodeM iset (encode (MInstruction inst)) = inst.
Proof.
  prove_decode_encode.
Qed.

Lemma mdecodeA_encode: forall (inst: InstructionA) (iset: InstructionSet),
    verify (AInstruction inst) iset ->
    mdecodeA iset (encode (AInstruction inst)) = inst.
Proof.
  prove_decode_encode.
Qed.

Lemma mdecodeF_encode: forall (inst: InstructionF) (iset: InstructionSet),
    verify (FInstruction inst) iset ->
    mdecodeF iset (encode (FInstruction inst)) = inst.
Proof.
  prove_decode_encode.
Qed.

Lemma mdecodeI64_encode: forall (inst: InstructionI64) (iset: InstructionSet),
    verify (I64Instruction inst) iset ->
    mdecodeI64 iset (encode (I64Instruction inst)) = inst.
Proof.
  prove_decode_encode.
Qed.

Lemma mdecodeM64_encode: forall (inst: InstructionM64) (iset: InstructionSet),
    verify (M64Instruction inst) iset ->
    mdecodeM64 iset (encode (M64Instruction inst)) = inst.
Proof.
  prove_decode_encode.
Qed.

Lemma mdecodeA64_encode: forall (inst: InstructionA64) (iset: InstructionSet),
    verify (A64Instruction inst) iset ->
    mdecodeA64 iset (encode (A64Instruction inst)) = inst.
Proof.
  prove_decode_encode.
Qed.

Lemma mdecodeF64_encode: forall (inst: InstructionF64) (iset: InstructionSet),
    verify (F64Instruction inst) iset ->
    mdecodeF64 iset (encode (F64Instruction inst)) = inst.
Proof.
  prove_decode_encode.
Qed.

Lemma mdecodeCSR_encode: forall (inst: InstructionCSR) (iset: InstructionSet),
    verify (CSRInstruction inst) iset ->
    mdecodeCSR iset (encode (CSRInstruction inst)) = inst.
Proof.
  (* prove_decode_encode. *)
  (* TODO inst/iset swapped! *)
Admitted.

Lemma mdecodeM_I: forall inst iset,
    mdecodeM iset (encode (IInstruction inst)) = InvalidM.
Proof.
  intros. cbv beta delta [mdecodeM].
  (* bad idea: requires us to do the whole case splitting again *)
Abort.

Lemma decode_encode: forall (inst: Instruction) (iset: InstructionSet),
    verify inst iset ->
    decode iset (encode inst) = inst.
Proof.
  destruct inst; intros.
  - apply mdecodeI_encode in H.
    rewrite decode_alt.
    cbv beta delta [modular_decode].
    rewrite H.
    simpl.
    (* not sure if the "modular" approach pays off *)
Admitted.
