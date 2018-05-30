Require Import Coq.ZArith.BinInt.
Require Import bbv.Word.
Require Import riscv.Decode.
Require Import riscv.encode.Encode.
Require Import riscv.Utility.
Require Import Coq.omega.Omega.

Local Open Scope bool_scope.
Local Open Scope Z_scope.

Lemma invert_encode_InvalidInstruction: forall i,
  verify_Invalid i ->
  forall inst,
  encode_Invalid i = inst ->
  False.
Proof. intros. assumption. Qed.

(*
Lemma bitSlice_split: forall a start mid eend,
    bitSlice a start eend = bitSlice a start mid <|> bitSlice a mid eend.
Admitted.

Lemma encode_R_bound: forall {opcode rd rs1 rs2 funct3 funct7},
    verify_R opcode rd rs1 rs2 funct3 funct7 ->
    0 <= encode_R opcode rd rs1 rs2 funct3 funct7 < 2 ^ 32.
Proof.
  (* corresponding lemma for I does not hold if imm is negative, but we will make it
     positive to make it work *)
Admitted.

Lemma bitSlice_all: forall w eend,
    0 <= w < 2 ^ eend ->
    w = bitSlice w 0 eend.
Admitted.
*)
(*
Search Z.testbit.

(* give length? *)
Fixpoint positive_to_bits(p: positive): list bool :=
  match p with
  | xI q => true :: positive_to_bits q
  | xO q => false :: positive_to_bits q
  | xH => true :: nil
  end.

Eval cbv in positive_to_bits 6%positive.

Definition Z_to_bits(z: Z): list bool :=
  match z with
  | Z0 => nil
            | 

Search positive list.
 *)

(*
Lemma invert_lor_eq: forall,
    a <|> Z.shiftl start b = c <|> bitSlice d start eend ->
*)  

Eval cbv in (Z.modulo (-3) 8).
(*
111  -1
110  -2
101  -3
 *)

Definition bitSlice'(w start eend: Z): Z :=
  (w / 2 ^ start) mod (2 ^ (eend - start)).

Require Import List.

Module bitSliceTest.

  Import ListNotations.

  Definition l1 := [-17; -16; -10; -1; 0; 1; 2; 3; 8].
  Definition l2 := [0; 1; 2; 3; 4; 5; 6].
  Definition inputs: list (Z * (Z * Z)) := (list_prod l1 (list_prod l2 l2)).

  Goal (map (fun p => match p with
                      | (w, (start, eend)) => bitSlice w start eend
                      end)
            inputs) =
       (map (fun p => match p with
                      | (w, (start, eend)) => bitSlice' w start eend
                      end)
            inputs).
    cbv.
    reflexivity.
  Qed.

End bitSliceTest.

Lemma bitSlice_alt: forall w start eend,
    0 <= start <= eend ->
    bitSlice w start eend = bitSlice' w start eend.
Proof.
  intros. unfold bitSlice, bitSlice'.
  rewrite <- Z.land_ones by omega.
  rewrite <- Z.shiftr_div_pow2 by omega.
  f_equal.
  rewrite Z.shiftl_mul_pow2 by omega.
  rewrite Z.mul_comm.
  rewrite <- Z.opp_eq_mul_m1.
  replace (Z.lnot (- 2 ^ (eend - start))) with (2 ^ (eend - start) - 1).
  - rewrite Z.ones_equiv. reflexivity.
  - pose proof (Z.add_lnot_diag (- 2 ^ (eend - start))). omega.
Qed.

Definition signExtend'(l n: Z): Z := n - ((n / 2 ^ (l - 1)) mod 2) * 2 ^ l.

Definition signExtend_alt: forall l n,
    0 < l ->
    signExtend l n = signExtend' l n.
Proof.
  intros. unfold signExtend, signExtend'.
  destruct (Z.testbit n (l - 1)) eqn: E.
  - apply (f_equal Z.b2z) in E.
    rewrite Z.testbit_spec' in E by omega.
    rewrite E.
    rewrite Z.setbit_spec'.
    rewrite Z.lor_0_l.
    change (Z.b2z true) with 1.
    rewrite Z.mul_1_l.
    reflexivity.
  - apply (f_equal Z.b2z) in E.
    rewrite Z.testbit_spec' in E by omega.
    rewrite E.
    change (Z.b2z false) with 0.
    rewrite Z.mul_0_l.
    rewrite Z.sub_0_r.
    reflexivity.
Qed.

(* TODO replace Z.lor by + in my encoder, but what about usages in decoder? *)

Tactic Notation "so" tactic(f) :=
  match goal with
  | _: ?A |- _  => f A
  |       |- ?A => f A
  end.

Module ThanksFiatCrypto.
  Ltac div_mod_to_quot_rem_inequality_solver := omega.

  Ltac generalize_div_eucl x y :=
    let H := fresh in
    let H' := fresh in
    assert (H' : y <> 0) by div_mod_to_quot_rem_inequality_solver;
    generalize (Z.div_mod x y H'); clear H';
    first [ assert (H' : 0 < y) by div_mod_to_quot_rem_inequality_solver;
            generalize (Z.mod_pos_bound x y H'); clear H'
          | assert (H' : y < 0) by div_mod_to_quot_rem_inequality_solver;
            generalize (Z.mod_neg_bound x y H'); clear H'
          | assert (H' : y < 0 \/ 0 < y) by (apply Z.neg_pos_cases; div_mod_to_quot_rem_inequality_solver);
            let H'' := fresh in
            assert (H'' : y < x mod y <= 0 \/ 0 <= x mod y < y)
              by (destruct H'; [ left; apply Z.mod_neg_bound; assumption
                               | right; apply Z.mod_pos_bound; assumption ]);
            clear H'; revert H'' ];
    let q := fresh "q" in
    let r := fresh "r" in
    set (q := x / y) in *;
    set (r := x mod y) in *;
    clearbody q r.

  Ltac div_mod_to_quot_rem_step :=
    so fun hyporgoal => match hyporgoal with
    | context[?x / ?y] => generalize_div_eucl x y
    | context[?x mod ?y] => generalize_div_eucl x y
    end.

  Ltac div_mod_to_quot_rem := repeat div_mod_to_quot_rem_step; intros.

End ThanksFiatCrypto.

Ltac somega_pre :=
  rewrite? bitSlice_alt in * by omega; unfold bitSlice' in *;
  rewrite? signExtend_alt in * by omega; unfold signExtend';
  rewrite? Z.shiftl_mul_pow2 in * by omega;
  repeat (so fun hyporgoal => match hyporgoal with
     | context [2 ^ ?x] => let r := eval cbv in (2 ^ x) in change (2 ^ x) with r in *
  end);
  ThanksFiatCrypto.div_mod_to_quot_rem;
  repeat match goal with
         | z: ?T |- _ => progress change T with Z in *
         end.

(* omega which understands bitSlice and shift *)
Ltac somega := somega_pre; omega.

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
Proof.
  intros.
  unfold encode_R, verify_R in *.
  somega.
Qed.

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
Proof.
  intros.
  unfold encode_R_atomic, verify_R_atomic in *.
  somega.
Qed.

Lemma invert_encode_I: forall {opcode rd rs1 funct3 oimm12},
  verify_I opcode rd rs1 funct3 oimm12 ->
  forall inst,
  encode_I opcode rd rs1 funct3 oimm12 = inst ->
  opcode = bitSlice inst 0 7 /\
  funct3 = bitSlice inst 12 15 /\
  rd = bitSlice inst 7 12 /\
  rs1 = bitSlice inst 15 20 /\
  oimm12 = signExtend 12 (bitSlice inst 20 32).
Proof.
  intros. unfold encode_I, verify_I in *. somega.
Qed.

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
Proof.
  intros. unfold encode_I_shift_57, verify_I_shift_57 in *. somega.
Qed.

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
  assert (bitwidth = 32 \/ bitwidth = 64) by admit.
  (* TODO put additional hyp into verify *)
  somega.
Admitted.

Lemma invert_encode_I_system: forall {opcode rd rs1 funct3 funct12},
  verify_I_system opcode rd rs1 funct3 funct12 ->
  forall inst,
  encode_I_system opcode rd rs1 funct3 funct12 = inst ->
  opcode = bitSlice inst 0 7 /\
  funct3 = bitSlice inst 12 15 /\
  funct12 = bitSlice inst 20 32 /\
  rd = bitSlice inst 7 12 /\
  rs1 = bitSlice inst 15 20.
Proof.
  intros. unfold encode_I_system, verify_I_system in *. somega.
Qed.


Lemma mul_div2_undo_mod: forall a, 2 * (a / 2) = a - a mod 2.
Proof.
  intros.
  pose proof (Z.div_mod a 2).
  omega.
Qed.

Definition signExtend_alt': forall l n,
    0 < l ->
    (exists q, n / 2 ^ (l - 1) = 2 * q /\ signExtend l n = n) \/
    (exists q, n / 2 ^ (l - 1) = 2 * q + 1 /\ signExtend l n = n - 2 ^ l).
Proof.
  intros. rewrite signExtend_alt by assumption. unfold signExtend'.
  pose proof (Z.mod_pos_bound (n / 2 ^ (l - 1)) 2).
  assert ((n / 2 ^ (l - 1)) mod 2 = 0 \/ (n / 2 ^ (l - 1)) mod 2 = 1) as C by omega.
  destruct C as [C | C]; rewrite C.
  - left. exists (n / 2 ^ (l - 1) / 2). rewrite mul_div2_undo_mod. omega.
  - right. exists (n / 2 ^ (l - 1) / 2). rewrite mul_div2_undo_mod. omega.
Qed.

Lemma invert_encode_S: forall {opcode rs1 rs2 funct3 simm12},
  verify_S opcode rs1 rs2 funct3 simm12 ->
  forall inst,
  encode_S opcode rs1 rs2 funct3 simm12 = inst ->
  opcode = bitSlice inst 0 7 /\
  funct3 = bitSlice inst 12 15 /\
  rs1 = bitSlice inst 15 20 /\
  rs2 = bitSlice inst 20 25 /\
  simm12 = signExtend 12 (Z.shiftl (bitSlice inst 25 32) 5 <|> bitSlice inst 7 12).
Proof.
  intros. unfold encode_S, verify_S in *.
  assert (Z.land (Z.shiftl (bitSlice inst 25 32) 5) (bitSlice inst 7 12) = 0) as L. {
    apply Z.bits_inj.
    unfold Z.eqf.
    intro i.
    rewrite Z.bits_0.
    rewrite Z.land_spec.
    rewrite Bool.andb_false_iff.
    assert (i < 0 \/ 0 <= i < 5 \/ 5 <= i) as C by omega. destruct C as [C | [C | C]].
    - rewrite Z.testbit_neg_r; auto.
    - rewrite Z.shiftl_spec by omega.
      rewrite Z.testbit_neg_r by omega. auto.
    - right. rewrite bitSlice_alt by omega. unfold bitSlice'.
      apply Z.mod_pow2_bits_high.
      omega.
  }
  rewrite <- Z.lxor_lor by assumption.
  rewrite <- Z.add_nocarry_lxor by assumption.
  clear L.
  so fun hyporgoal => match hyporgoal with
  | context [signExtend ?l ?n] => destruct (signExtend_alt' l n) as [[q [E1 E2]] | [q [E1 E2]]];
                                  [ omega | rewrite E2 in * .. ]
  end.
  - somega_pre. omega.
  - somega_pre. omega.  
Qed.

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
Proof. Admitted.

Lemma invert_encode_U: forall {opcode rd imm20},
  verify_U opcode rd imm20 ->
  forall inst,
  encode_U opcode rd imm20 = inst ->
  opcode = bitSlice inst 0 7 /\
  rd = bitSlice inst 7 12 /\
  imm20 = signExtend 32 (Z.shiftl (bitSlice inst 12 32) 12).
Proof.
  intros. unfold encode_U, verify_U in *. somega_pre.
  (* TODO there are still some mod and div left! *)
Admitted.

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
Proof. Admitted.

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
Proof.
  intros. unfold encode_Fence, verify_Fence in *. somega.
Qed.

Ltac prove_andb_false :=
  reflexivity ||
  assumption ||
  (symmetry; assumption) ||
  (apply Bool.andb_false_intro1; prove_andb_false) ||
  (apply Bool.andb_false_intro2; prove_andb_false).
  
Goal forall b1 b3 b4 b5, b1 && false && b3 && b4 && b5 = false. intros. prove_andb_false. Qed.
Goal forall b1 b2 b4 b5, b1 && (b2 && false) && b4 && b5 = false. intros. prove_andb_false. Qed.
Goal forall b1 b3 b4 b5, (b1 && (false && b3) && b4) && b5 = false. intros. prove_andb_false. Qed.

Lemma andb_true: forall b1 b2,
    b1 = true -> b2 = true -> b1 && b2 = true.
Proof. intros. subst. reflexivity. Qed.

Ltac prove_andb_true :=
  reflexivity ||
  assumption ||
  (symmetry; assumption) ||
  (apply andb_true; prove_andb_true).

Goal forall b1 b2, b1 = true -> b2 = true -> true && b1 && (b2 && true) = true.
  intros. prove_andb_true.
Qed.

Ltac cbn_encode := repeat (
    cbn [
      Z.eqb Pos.eqb andb
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
cbv [machineIntToShamt id] in *).

Definition TODO{T: Type}: T. Admitted.

Lemma decode_encode (inst: Instruction) (z: Z) (H:respects_bounds 64 inst) :
    decode RV64IMA (encode inst) = inst.
Proof.
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
  (* TODO: use par:abstract here once all of the proof is automated into the next sentence *)
  all: destruct i; try (
    (lazymatch type of Henc with
     | encode_I _ _ _ _ _ = _ =>
       apply invert_encode_I in Henc
     | encode_Fence _ _ _ _ _ _ _ = _ =>
       apply invert_encode_Fence in Henc
     | encode_I_shift_66 _ _ _ _ _ _ = _ =>
       apply (invert_encode_I_shift_66(bitwidth:=64)) in Henc
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
      repeat match goal with
      | H: False |- _ => destruct H
      | |- ?x = ?x => exact_no_check (eq_refl x)
      | |- _ => progress cbn_encode
      | |- _ => rewrite !Bool.orb_true_r in *
      | |- _ => rewrite !Bool.andb_false_r in *
      | |- _ => progress subst
      end).

  (* cases where bitSlice in goal and hyps do not match (but the encoded value is fully specified) *)
  all : cbv [funct7_SFENCE_VMA opcode_SYSTEM funct3_PRIV funct12_WFI funct12_MRET funct12_SRET funct12_URET funct12_EBREAK funct12_ECALL funct3_FENCE_I opcode_MISC_MEM isValidI] in *.
  all:
    repeat match goal with
           | |- ?x = ?x => exact_no_check (eq_refl x)
           | |- context [?x =? ?y] =>
             let H := fresh "H" in
             destruct (x =? y) eqn:H;
               apply Z.eqb_eq in H || apply Z.eqb_neq in H
           | _ => progress cbn in *
           end.
  all : exfalso; try match goal with H: _ <> _ |- _ => apply H; clear H end.
  (* 7 subgoals (ID 91796) *)
  
(*   z : Z *)
(*   H : verify_Fence opcode_MISC_MEM 0 0 funct3_FENCE_I 0 0 0 *)
(*   encoded : MachineInt *)
(*   H43 : 15 = bitSlice encoded 0 7 *)
(*   H44 : 1 = bitSlice encoded 12 15 *)
(*   H45 : 0 = bitSlice encoded 7 12 *)
(*   H46 : 0 = bitSlice encoded 15 20 *)
(*   H47 : 0 = bitSlice encoded 20 24 *)
(*   H48 : 0 = bitSlice encoded 24 28 *)
(*   Henc : 0 = bitSlice encoded 28 32 *)
(*   ============================ *)
(*   signExtend 12 (bitSlice encoded 20 32) = 0 *)

  apply TODO.

(* 6 subgoals (ID 91789) *)
  
(*   z : Z *)
(*   H : verify_I_system opcode_SYSTEM 0 0 funct3_PRIV funct12_ECALL *)
(*   encoded : MachineInt *)
(*   H43 : 115 = bitSlice encoded 0 7 *)
(*   H44 : 0 = bitSlice encoded 12 15 *)
(*   H45 : 0 = bitSlice encoded 20 32 *)
(*   H46 : 0 = bitSlice encoded 7 12 *)
(*   Henc : 0 = bitSlice encoded 15 20 *)
(*   H0 : bitSlice encoded 25 32 = 9 *)
(*   ============================ *)
(*   False *)

  apply TODO.

 (* 5 subgoals (ID 91790) *)
  
(*   z : Z *)
(*   H : verify_I_system opcode_SYSTEM 0 0 funct3_PRIV funct12_EBREAK *)
(*   encoded : MachineInt *)
(*   H43 : 115 = bitSlice encoded 0 7 *)
(*   H44 : 0 = bitSlice encoded 12 15 *)
(*   H45 : 1 = bitSlice encoded 20 32 *)
(*   H46 : 0 = bitSlice encoded 7 12 *)
(*   Henc : 0 = bitSlice encoded 15 20 *)
(*   H0 : bitSlice encoded 25 32 = 9 *)
(*   ============================ *)
(*   False *)
  
  apply TODO.
(* 4 subgoals (ID 91791) *)
  
(*   z : Z *)
(*   H : verify_I_system opcode_SYSTEM 0 0 funct3_PRIV funct12_URET *)
(*   encoded : MachineInt *)
(*   H43 : 115 = bitSlice encoded 0 7 *)
(*   H44 : 0 = bitSlice encoded 12 15 *)
(*   H45 : 2 = bitSlice encoded 20 32 *)
(*   H46 : 0 = bitSlice encoded 7 12 *)
(*   Henc : 0 = bitSlice encoded 15 20 *)
(*   H0 : bitSlice encoded 25 32 = 9 *)
(*   ============================ *)
(*   False *)

  apply TODO.
  (* 3 subgoals (ID 91792) *)
  
(*   z : Z *)
(*   H : verify_I_system opcode_SYSTEM 0 0 funct3_PRIV funct12_SRET *)
(*   encoded : MachineInt *)
(*   H43 : 115 = bitSlice encoded 0 7 *)
(*   H44 : 0 = bitSlice encoded 12 15 *)
(*   H45 : 258 = bitSlice encoded 20 32 *)
(*   H46 : 0 = bitSlice encoded 7 12 *)
(*   Henc : 0 = bitSlice encoded 15 20 *)
(*   H0 : bitSlice encoded 25 32 = 9 *)
(*   ============================ *)
(*   False *)
  apply TODO.
  (* 2 subgoals (ID 91793) *)
  
(*   z : Z *)
(*   H : verify_I_system opcode_SYSTEM 0 0 funct3_PRIV funct12_MRET *)
(*   encoded : MachineInt *)
(*   H43 : 115 = bitSlice encoded 0 7 *)
(*   H44 : 0 = bitSlice encoded 12 15 *)
(*   H45 : 770 = bitSlice encoded 20 32 *)
(*   H46 : 0 = bitSlice encoded 7 12 *)
(*   Henc : 0 = bitSlice encoded 15 20 *)
(*   H0 : bitSlice encoded 25 32 = 9 *)
(*   ============================ *)
(*   False *)
  apply TODO.
  (* 1 subgoal (ID 91794) *)
  
  (* z : Z *)
  (* H : verify_I_system opcode_SYSTEM 0 0 funct3_PRIV funct12_WFI *)
  (* encoded : MachineInt *)
  (* H43 : 115 = bitSlice encoded 0 7 *)
  (* H44 : 0 = bitSlice encoded 12 15 *)
  (* H45 : 261 = bitSlice encoded 20 32 *)
  (* H46 : 0 = bitSlice encoded 7 12 *)
  (* Henc : 0 = bitSlice encoded 15 20 *)
  (* H0 : bitSlice encoded 25 32 = 9 *)
  (* ============================ *)
  (* False *)
  apply TODO.
Time Qed.
