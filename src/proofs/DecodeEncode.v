Require Import Coq.ZArith.BinInt.
Require Import Coq.omega.Omega.
Require Import Coq.micromega.Lia.
Require Import bbv.Word.
Require Import riscv.Decode.
Require Import riscv.encode.Encode.
Require Import riscv.Utility.
Require Import riscv.util.Tactics.
Require Import riscv.util.div_mod_to_quot_rem.
Require Import riscv.proofs.prove_Zeq_bitwise.

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

Ltac write_as_pow2_opportunities f :=
    repeat (so fun hyporgoal => match hyporgoal with
               | context [ Z.pos ?p ] =>
                   match p with
                   | 1%positive => fail 1
                   | 2%positive => fail 1
                   | _ => idtac
                   end;
                   let e := eval cbv in (Z.log2 (Z.pos p)) in
                   f (Z.pos p) (2 ^ e)
               end);
    (* we might have been a bit too eager -- undo undesired chained powers: *)
    repeat (so fun hyporgoal => match hyporgoal with
               | context [2 ^ 2 ^ ?p] => let r := eval cbv in (2 ^ p) in
                                         change (2 ^ 2 ^ p) with (2 ^ r) in *
               end).

Tactic Notation "write_as_pow2" "in" "*|-" :=
  write_as_pow2_opportunities ltac:(fun old new => change old with new in *|-).

Tactic Notation "write_as_pow2" "in" "*" :=
  write_as_pow2_opportunities ltac:(fun old new => change old with new in *).

Lemma invert_encode_InvalidInstruction: forall i,
  verify_Invalid i ->
  forall inst,
  encode_Invalid i = inst ->
  False.
Proof. intros. assumption. Qed.

Lemma invert_encode_R: forall {opcode rd rs1 rs2 funct3 funct7},
  verify_R opcode rd rs1 rs2 funct3 funct7 ->
  forall inst,
  encode_R opcode rd rs1 rs2 funct3 funct7 = inst ->
  opcode = bitSlice inst 0 7 /\
  funct3 = bitSlice inst 12 15 /\
  funct7 = bitSlice inst 25 32 /\
  rd = bitSlice inst 7 12 /\
  rs1 = bitSlice inst 15 20 /\
  rs2 = bitSlice inst 20 25.
Proof. intros. unfold encode_R, verify_R in *. prove_Zeq_bitwise. Qed.

Lemma invert_encode_R_atomic: forall {opcode rd rs1 rs2 funct3 aqrl funct5},
  verify_R_atomic opcode rd rs1 rs2 funct3 aqrl funct5 ->
  forall inst,
  encode_R_atomic opcode rd rs1 rs2 funct3 aqrl funct5 = inst ->
  opcode = bitSlice inst 0 7 /\
  funct3 = bitSlice inst 12 15 /\
  aqrl = bitSlice inst 25 27 /\
  funct5 = bitSlice inst 27 32 /\
  rd = bitSlice inst 7 12 /\
  rs1 = bitSlice inst 15 20 /\
  rs2 = bitSlice inst 20 25.
Proof. intros. unfold encode_R_atomic, verify_R_atomic in *. prove_Zeq_bitwise. Qed.

Lemma invert_encode_I: forall {opcode rd rs1 funct3 oimm12},
  verify_I opcode rd rs1 funct3 oimm12 ->
  forall inst,
  encode_I opcode rd rs1 funct3 oimm12 = inst ->
  opcode = bitSlice inst 0 7 /\
  funct3 = bitSlice inst 12 15 /\
  rd = bitSlice inst 7 12 /\
  rs1 = bitSlice inst 15 20 /\
  oimm12 = signExtend 12 (bitSlice inst 20 32).
Proof. intros. unfold encode_I, verify_I in *. prove_Zeq_bitwise. Qed.

Lemma invert_encode_I_shift_57: forall {opcode rd rs1 shamt5 funct3 funct7},
  verify_I_shift_57 opcode rd rs1 shamt5 funct3 funct7 ->
  forall inst,
  encode_I_shift_57 opcode rd rs1 shamt5 funct3 funct7 = inst ->
  opcode = bitSlice inst 0 7 /\
  funct3 = bitSlice inst 12 15 /\
  funct7 = bitSlice inst 25 32 /\
  rd = bitSlice inst 7 12 /\
  rs1 = bitSlice inst 15 20 /\
  shamt5 = bitSlice inst 20 25.
Proof. intros. unfold encode_I_shift_57, verify_I_shift_57 in *. prove_Zeq_bitwise. Qed.

Lemma invert_encode_I_shift_66: forall {bitwidth opcode rd rs1 shamt6 funct3 funct6},
  verify_I_shift_66 bitwidth opcode rd rs1 shamt6 funct3 funct6 ->
  forall inst,
  encode_I_shift_66  opcode rd rs1 shamt6 funct3 funct6 = inst ->
  opcode = bitSlice inst 0 7 /\
  funct3 = bitSlice inst 12 15 /\
  funct6 = bitSlice inst 26 32 /\
  rd = bitSlice inst 7 12 /\
  rs1 = bitSlice inst 15 20 /\
  shamt6 = bitSlice inst 20 26 /\
  ((Z.eqb (bitSlice inst 25 26) 0) || (Z.eqb bitwidth 64)) = true.
Proof.
  intros. unfold encode_I_shift_66, verify_I_shift_66 in *.
  rewrite Bool.orb_true_iff.
  rewrite? Z.eqb_eq.
  prove_Zeq_bitwise.
Qed.

Lemma invert_encode_I_system: forall {opcode rd rs1 funct3 funct12},
  verify_I_system opcode rd rs1 funct3 funct12 ->
  forall inst,
  encode_I_system opcode rd rs1 funct3 funct12 = inst ->
  opcode = bitSlice inst 0 7 /\
  funct3 = bitSlice inst 12 15 /\
  funct12 = bitSlice inst 20 32 /\
  rd = bitSlice inst 7 12 /\
  rs1 = bitSlice inst 15 20.
Proof. intros. unfold encode_I_system, verify_I_system in *. prove_Zeq_bitwise. Qed.

Lemma invert_encode_S: forall {opcode rs1 rs2 funct3 simm12},
  verify_S opcode rs1 rs2 funct3 simm12 ->
  forall inst,
  encode_S opcode rs1 rs2 funct3 simm12 = inst ->
  opcode = bitSlice inst 0 7 /\
  funct3 = bitSlice inst 12 15 /\
  rs1 = bitSlice inst 15 20 /\
  rs2 = bitSlice inst 20 25 /\
  simm12 = signExtend 12 (Z.shiftl (bitSlice inst 25 32) 5 <|> bitSlice inst 7 12).
Proof. intros. unfold encode_S, verify_S in *. prove_Zeq_bitwise. Qed.

Lemma invert_encode_SB: forall {opcode rs1 rs2 funct3 sbimm12},
  verify_SB opcode rs1 rs2 funct3 sbimm12 ->
  forall inst,
  encode_SB opcode rs1 rs2 funct3 sbimm12 = inst ->
  opcode = bitSlice inst 0 7 /\
  funct3 = bitSlice inst 12 15 /\
  rs1 = bitSlice inst 15 20 /\
  rs2 = bitSlice inst 20 25 /\
  sbimm12 = signExtend 13 (Z.shiftl (bitSlice inst 31 32) 12 <|>
                           Z.shiftl (bitSlice inst 25 31) 5 <|>
                           Z.shiftl (bitSlice inst 8 12) 1  <|>
                           Z.shiftl (bitSlice inst 7 8) 11).
Proof. intros. unfold encode_SB, verify_SB in *. prove_Zeq_bitwise. Qed.

Lemma invert_encode_U: forall {opcode rd imm20},
  verify_U opcode rd imm20 ->
  forall inst,
  encode_U opcode rd imm20 = inst ->
  opcode = bitSlice inst 0 7 /\
  rd = bitSlice inst 7 12 /\
  imm20 = signExtend 32 (Z.shiftl (bitSlice inst 12 32) 12).
Proof. intros. unfold encode_U, verify_U in *. prove_Zeq_bitwise. Qed.

Lemma invert_encode_UJ: forall {opcode rd jimm20},
  verify_UJ opcode rd jimm20 ->
  forall inst,
  encode_UJ opcode rd jimm20 = inst ->
  opcode = bitSlice inst 0 7 /\
  rd = bitSlice inst 7 12 /\
  jimm20 = signExtend 21 (Z.shiftl (bitSlice inst 31 32) 20  <|>
                          Z.shiftl (bitSlice inst 21 31) 1  <|>
                          Z.shiftl (bitSlice inst 20 21) 11 <|>
                          Z.shiftl (bitSlice inst 12 20) 12).
Proof. intros. unfold encode_UJ, verify_UJ in *. prove_Zeq_bitwise. Qed.

Lemma invert_encode_Fence: forall {opcode rd rs1 funct3 prd scc msb4},
  verify_Fence opcode rd rs1 funct3 prd scc msb4 ->
  forall inst,
  encode_Fence opcode rd rs1 funct3 prd scc msb4 = inst ->
  opcode = bitSlice inst 0 7 /\
  funct3 = bitSlice inst 12 15 /\
  rd = bitSlice inst 7 12 /\
  rs1 = bitSlice inst 15 20 /\
  scc = bitSlice inst 20 24 /\
  prd = bitSlice inst 24 28 /\
  msb4 = bitSlice inst 28 32.
Proof. intros. unfold encode_Fence, verify_Fence in *. prove_Zeq_bitwise. Qed.

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
    funct3_JALR
    funct7_XOR
    funct7_SUBW
    funct7_SRLIW
    funct7_SRL
    funct7_SUB
    funct7_SRLW
    funct7_SRA
    funct7_SLTU
    funct7_SLT
    funct7_SLLW
    funct7_SLLIW
    funct7_SLL
    funct7_SRAW
    funct7_SRAIW
    funct7_MUL
    funct7_DIVW
    funct7_DIVUW
    funct7_DIVU
    funct7_DIV
    funct7_AND
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
    funct3_SRAIW
    funct3_SRAI
    funct3_SRA
    funct3_SLTU
    funct3_SLTIU
    funct3_SLTI
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
    funct12_EBREAK
    funct3_DIVUW
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
    funct3_FENCE_I
    funct3_FENCE
    funct3_DIVW
    funct3_AND
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
    funct12_URET
    funct3_AMOW
    funct3_AMOD
    funct3_ADDW
    funct3_ADDIW
    funct3_ADDI
    funct3_ADD
    funct12_WFI
    funct12_MRET
    funct12_SRET
    funct12_ECALL
    isValidM64
    isValidM
    isValidI64
    isValidI
    isValidCSR
    isValidA64
    isValidA
    supportsM
    supportsA
    bitwidth
    app
  ] in *;
  cbv [machineIntToShamt id] in *
).

Lemma decode_encode: forall (inst: Instruction) (iset: InstructionSet),
    verify inst iset ->
    decode iset (encode inst) = inst.
Proof.
  intros. unfold verify in H. destruct H as [H H0].
  unfold verify_iset in *.
  cbv beta delta [decode].
  repeat match goal with
  | |- (let x := ?a in ?b) = ?c => change (let x := a in b = c); intro
  | x := ?t : ?T |- _ => pose proof (eq_refl t : x = t); clearbody x
  end.
  remember (encode inst) as encoded eqn:Henc; symmetry in Henc.
  cbv [encode] in Henc.
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
    ] in Henc.

  destruct inst as [i|i|i|i|i|i|i|i].
  par: abstract (destruct i; try (
    (lazymatch type of Henc with
     | encode_I _ _ _ _ _ = _ =>
       apply invert_encode_I in Henc
     | encode_Fence _ _ _ _ _ _ _ = _ =>
       apply invert_encode_Fence in Henc
     | encode_I_shift_66 _ _ _ _ _ _ = _ =>
       apply (@invert_encode_I_shift_66 (bitwidth iset)) in Henc
     | encode_I_shift_57 _ _ _ _ _ _ = _ =>
       apply invert_encode_I_shift_57 in Henc
     | encode_R _ _ _ _ _ _ = _ =>
       apply invert_encode_R in Henc
     | encode_Invalid _ = _ =>
       apply invert_encode_InvalidInstruction in Henc
     | encode_R_atomic _ _ _ _ _ _ _ = _ => 
       apply invert_encode_R_atomic in Henc
     | encode_I_system _ _ _ _ _ = _ =>
       apply invert_encode_I_system in Henc
     | encode_U _ _ _ = _ =>
       apply invert_encode_U in Henc
     | encode_UJ _ _ _ = _ =>
       apply invert_encode_UJ in Henc
     | encode_S _ _ _ _ _ = _ =>
       apply invert_encode_S in Henc
     | encode_SB _ _ _ _ _ = _ => 
       apply invert_encode_SB in Henc
     end; [|trivial]);
      repeat match type of Henc with
               _ /\ _ => let H := fresh "H" in destruct Henc as [H Henc]; rewrite <-?H in *
             end; rewrite <-?Henc in *;
      subst results; subst resultI; subst decodeI; subst opcode; subst funct3;
      subst funct5; subst funct6; subst funct7; subst funct10; subst funct12;
      destruct iset;
      repeat match goal with
      | H: False |- _ => destruct H
      | |- ?x = ?x => exact_no_check (eq_refl x)
      | |- _ => progress cbn_encode
      | |- _ => rewrite !Bool.orb_true_r in *
      | |- _ => rewrite !Bool.andb_false_r in *
      | |- _ => progress subst
      end);
     (* cases where bitSlice in goal and hyps do not match *)
     cbv [funct7_SFENCE_VMA opcode_SYSTEM funct3_PRIV funct12_WFI funct12_MRET
          funct12_SRET funct12_URET funct12_EBREAK funct12_ECALL
          funct3_FENCE_I opcode_MISC_MEM isValidI] in *;
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
Qed.

Print Assumptions decode_encode.
