Require Export Coq.ZArith.ZArith.
Require Export Coq.Lists.List. Import ListNotations.
Require Import coqutil.Tactics.rdelta.
Require Import coqutil.Tactics.destr.
Require Import coqutil.Z.prove_Zeq_bitwise.
Require Import coqutil.Tactics.Tactics.
Require Export riscv.Spec.Decode.
Require Export riscv.Utility.Encode.
Require Export riscv.Utility.Utility.
Require Import riscv.Proofs.DecodeByExtension.

Local Open Scope Z_scope.

Local Ltac t :=
  intros;
  match goal with
  | |- ?l = _ => let h := head l in unfold h
  end;
  prove_Zeq_bitwise.

Lemma encode_decode_I: forall inst,
    0 <= inst < 2 ^ 32 ->
    encode_I (bitSlice inst 0 7)
             (bitSlice inst 7 12)
             (bitSlice inst 15 20)
             (bitSlice inst 12 15)
             (signExtend 12 (bitSlice inst 20 32)) = inst.
Proof. t. Qed.

Lemma encode_decode_I_shift_66: forall inst,
    0 <= inst < 2 ^ 32 ->
    encode_I_shift_66 (bitSlice inst 0 7)
                      (bitSlice inst 7 12)
                      (bitSlice inst 15 20)
                      (bitSlice inst 20 26)
                      (bitSlice inst 12 15)
                      (bitSlice inst 26 32) = inst.
Proof. t. Qed.

Lemma encode_decode_I_shift_57: forall inst,
    0 <= inst < 2 ^ 32 ->
    encode_I_shift_57 (bitSlice inst 0 7)
                      (bitSlice inst 7 12)
                      (bitSlice inst 15 20)
                      (bitSlice inst 20 25)
                      (bitSlice inst 12 15)
                      (bitSlice inst 25 32) = inst.
Proof. t. Qed.

Lemma encode_decode_I_system: forall inst,
    0 <= inst < 2 ^ 32 ->
    encode_I_system (bitSlice inst 0 7)
                    (bitSlice inst 7 12)
                    (bitSlice inst 15 20)
                    (bitSlice inst 12 15)
                    (bitSlice inst 20 32) = inst.
Proof. t. Qed.

Lemma encode_decode_U: forall inst,
    0 <= inst < 2 ^ 32 ->
    encode_U (bitSlice inst 0 7)
             (bitSlice inst 7 12)
             (signExtend 32 (BinInt.Z.shiftl (bitSlice inst 12 32) 12)) = inst.
Proof. t. Qed.

Lemma encode_decode_UJ: forall inst,
    0 <= inst < 2 ^ 32 ->
    encode_UJ (bitSlice inst 0 7) (bitSlice inst 7 12)
              (signExtend 21 (Z.shiftl (bitSlice inst 31 32) 20 <|>
                              Z.shiftl (bitSlice inst 21 31) 1 <|>
                              Z.shiftl (bitSlice inst 20 21) 11 <|>
                              Z.shiftl (bitSlice inst 12 20) 12)) = inst.
Proof. t. Qed.

Lemma encode_decode_S: forall inst,
    0 <= inst < 2 ^ 32 ->
    encode_S
      (bitSlice inst 0 7)
      (bitSlice inst 15 20)
      (bitSlice inst 20 25)
      (bitSlice inst 12 15)
      (signExtend 12 (Z.shiftl (bitSlice inst 25 32) 5 <|> bitSlice inst 7 12)) = inst.
Proof. t. Qed.

Lemma encode_decode_SB: forall inst,
    0 <= inst < 2 ^ 32 ->
    encode_SB (bitSlice inst 0 7)
              (bitSlice inst 15 20)
              (bitSlice inst 20 25)
              (bitSlice inst 12 15)
              (signExtend 13 (Z.shiftl (bitSlice inst 31 32) 12 <|>
                              Z.shiftl (bitSlice inst 25 31) 5 <|>
                              Z.shiftl (bitSlice inst 8 12) 1 <|>
                              Z.shiftl (bitSlice inst 7 8) 11)) = inst.
Proof. t. Qed.

Lemma encode_decode_R: forall inst,
    0 <= inst < 2 ^ 32 ->
    encode_R (bitSlice inst 0 7)
             (bitSlice inst 7 12)
             (bitSlice inst 15 20)
             (bitSlice inst 20 25)
             (bitSlice inst 12 15)
             (bitSlice inst 25 32) = inst.
Proof. t. Qed.

Lemma encode_decode_Fence: forall inst,
    0 <= inst < 2 ^ 32 ->
    encode_Fence (bitSlice inst 0 7)
                 (bitSlice inst 7 12)
                 (bitSlice inst 15 20)
                 (bitSlice inst 12 15)
                 (bitSlice inst 24 28)
                 (bitSlice inst 20 24)
                 (bitSlice inst 28 32) = inst.
Proof. t. Qed.

Lemma encode_decode_FenceI: forall inst,
    0 <= inst < 2 ^ 32 ->
    encode_FenceI (bitSlice inst 0 7)
                  (bitSlice inst 7 12)
                  (bitSlice inst 15 20)
                  (bitSlice inst 12 15)
                  (signExtend 12 (bitSlice inst 20 32)) = inst.
Proof. t. Qed.

Lemma encode_decode_R_atomic: forall inst,
    0 <= inst < 2 ^ 32 ->
    encode_R_atomic (bitSlice inst 0 7)
                    (bitSlice inst 7 12)
                    (bitSlice inst 15 20)
                    (bitSlice inst 20 25)
                    (bitSlice inst 12 15)
                    (bitSlice inst 25 27)
                    (bitSlice inst 27 32) = inst.
Proof. t. Qed.

Lemma encode_decode_Invalid: forall inst,
    0 <= inst < 2 ^ 32 ->
    encode_Invalid inst = inst.
Proof. t. Qed.

Ltac apply_encode_decode_lemma :=
  match goal with
  | |- encode_I _ _ _ _ _ = _ =>
      eqapply encode_decode_I; [assumption|f_equal;assumption]
  | |- encode_I_shift_66 _ _ _ _ _ _ = _ =>
      eqapply encode_decode_I_shift_66; [assumption|f_equal;assumption]
  | |- encode_I_shift_57 _ _ _ _ _ _ = _ =>
      eqapply encode_decode_I_shift_57; [assumption|f_equal;assumption]
  | |- encode_I_system _ _ _ _ _ = _ =>
      eqapply encode_decode_I_system; [assumption|f_equal;assumption]
  | |- encode_U _ _ _ = _ =>
      eqapply encode_decode_U; [assumption|f_equal;assumption]
  | |- encode_UJ _ _ _ = _ =>
      eqapply encode_decode_UJ; [assumption|f_equal;assumption]
  | |- encode_S _ _ _ _ _ = _ =>
      eqapply encode_decode_S; [assumption|f_equal;assumption]
  | |- encode_SB _ _ _ _ _ = _ =>
      eqapply encode_decode_SB; [assumption|f_equal;assumption]
  | |- encode_R _ _ _ _ _ _ = _ =>
      eqapply encode_decode_R; [assumption|f_equal;assumption]
  | |- encode_R_atomic _ _ _ _ _ _ _ = _ =>
      eqapply encode_decode_R_atomic; [assumption|f_equal;assumption]
  | |- encode_Fence _ _ _ _ _ _ _ = _ =>
      eqapply encode_decode_Fence; [assumption|f_equal;assumption]
  | |- encode_FenceI _ _ _ _ _ = _ =>
      eqapply encode_decode_FenceI; [assumption|f_equal;assumption]
  | |- encode_Invalid _ = _ =>
      apply encode_decode_Invalid; assumption
  end.

Axiom TODO_spec_bug: False.

Lemma if_same{A: Type}: forall (b: bool) (a: A), (if b then a else a) = a.
Proof. destruct b; reflexivity. Qed.

Lemma encode_decode: forall iset inst,
    supportsF iset = false -> (* encoder does not yet support F extension *)
    0 <= inst < 2 ^ 32 ->
    encode (decode iset inst) = inst.
Proof.
  intros *. intro F_not_supported. intros. rewrite <- decode_alt_correct.
  cbv beta delta [decode_alt decode_results].
  cbv beta delta [decode_resultI decode_resultM decode_resultA decode_resultF
                  decode_resultI64 decode_resultM64 decode_resultA64 decode_resultF64
                  decode_resultCSR].
  cbv zeta.
  cbv beta delta [decodeI decodeM decodeA decodeF
                  decodeI64 decodeM64 decodeA64 decodeF64
                  decodeCSR].
  cbv zeta.
  refine (id _).
  loop INil.
  all: try abstract (
       match goal with
       | |- encode (nth 0 ?l ?d) = _ =>
           rewrite ?if_same
       end;
       repeat match goal with
              | |- context[if ?supports ?iset then _ else _] =>
                  lazymatch type of iset with
                  | InstructionSet => destr (supports iset)
                  end
              end;
       match goal with
       | |- encode (nth 0 ?l ?d) = _ =>
          let r := eval hnf in (nth 0 l d) in
          let h := head r in
          tryif is_constructor h then
            change (nth 0 l d) with r
          else
            fail "hnf did not return a term starting with a constructor, but" r
       end;
       cbv beta iota zeta delta [encode apply_InstructionMapper Encoder
           map_Invalid map_R map_R_atomic map_I map_I_shift_57 map_I_shift_66
           map_I_system map_S map_SB map_U map_UJ map_Fence map_FenceI
       ];
       try apply_encode_decode_lemma;
       try match goal with
           | H: true = false |- _ => discriminate H
           end).
  {
    case TODO_spec_bug.
  }
  {
    case TODO_spec_bug.
  }
Time Defined. (* 941.462 secs *)
