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

Lemma bitSlice_alt: forall w start eend, bitSlice w start eend = bitSlice' w start eend.
Admitted.

(* TODO replace Z.lor by + in my encoder, but what about usages in decoder? *)

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
    match goal with
    | [ |- context[?x / ?y] ] => generalize_div_eucl x y
    | [ |- context[?x mod ?y] ] => generalize_div_eucl x y
    end.

  Ltac div_mod_to_quot_rem := repeat div_mod_to_quot_rem_step; intros.

End ThanksFiatCrypto.

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
  rewrite? bitSlice_alt in *. unfold bitSlice' in *.
  rewrite? Z.shiftl_mul_pow2 in * by omega.
  repeat match goal with
         | _: context [2 ^ ?x] |- _ => let r := eval cbv in (2 ^ x) in change (2 ^ x) with r in *
         | |- context [2 ^ ?x]      => let r := eval cbv in (2 ^ x) in change (2 ^ x) with r in *
         end.
  ThanksFiatCrypto.div_mod_to_quot_rem.
  unfold MachineInt, Register in *.
  omega.
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
Proof. Admitted.

Lemma invert_encode_I: forall {opcode rd rs1 funct3 oimm12},
  verify_I opcode rd rs1 funct3 oimm12 ->
  forall inst,
  encode_I opcode rd rs1 funct3 oimm12 = inst ->
  opcode = bitSlice inst 0 7 /\
  funct3 = bitSlice inst 12 15 /\
  rd = bitSlice inst 7 12 /\
  rs1 = bitSlice inst 15 20 /\
  oimm12 = signExtend 12 (bitSlice inst 20 32).
Proof. Admitted.

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
Proof. Admitted.

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
Proof. Admitted.

Lemma invert_encode_I_system: forall {opcode rd rs1 funct3 funct12},
  verify_I_system opcode rd rs1 funct3 funct12 ->
  forall inst,
  encode_I_system opcode rd rs1 funct3 funct12 = inst ->
  opcode = bitSlice inst 0 7 /\
  funct3 = bitSlice inst 12 15 /\
  funct12 = bitSlice inst 20 32 /\
  rd = bitSlice inst 7 12 /\
  rs1 = bitSlice inst 15 20.
Proof. Admitted.

Lemma invert_encode_S: forall {opcode rs1 rs2 funct3 simm12},
  verify_S opcode rs1 rs2 funct3 simm12 ->
  forall inst,
  encode_S opcode rs1 rs2 funct3 simm12 = inst ->
  opcode = bitSlice inst 0 7 /\
  funct3 = bitSlice inst 12 15 /\
  rs1 = bitSlice inst 15 20 /\
  rs2 = bitSlice inst 20 25 /\
  simm12 = signExtend 12 (Z.shiftl (bitSlice inst 25 32) 5 <|> bitSlice inst 7 12).
Proof. Admitted.

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
Proof. Admitted.

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
Proof. Admitted.

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

Ltac invert_encode :=
  match goal with
  | V: context[verify_Invalid   ], H: _ |- _ => pose proof (invert_encode_InvalidInstruction V _ H)
  | V: context[verify_R         ], H: _ |- _ => pose proof (invert_encode_R                  V _ H)
  | V: context[verify_R_atomic  ], H: _ |- _ => pose proof (invert_encode_R_atomic           V _ H)
  | V: context[verify_I         ], H: _ |- _ => pose proof (invert_encode_I                  V _ H)
  | V: context[verify_I_shift_57], H: _ |- _ => pose proof (invert_encode_I_shift_57         V _ H)
  | V: context[verify_I_shift_66], H: _ |- _ => pose proof (invert_encode_I_shift_66         V _ H)
  | V: context[verify_I_system  ], H: _ |- _ => pose proof (invert_encode_I_system           V _ H)
  | V: context[verify_S         ], H: _ |- _ => pose proof (invert_encode_S                  V _ H)
  | V: context[verify_SB        ], H: _ |- _ => pose proof (invert_encode_SB                 V _ H)
  | V: context[verify_U         ], H: _ |- _ => pose proof (invert_encode_U                  V _ H)
  | V: context[verify_UJ        ], H: _ |- _ => pose proof (invert_encode_UJ                 V _ H)
  | V: context[verify_Fence     ], H: _ |- _ => pose proof (invert_encode_Fence              V _ H)
  end.


Lemma pull_let: forall {A B: Type} (a: A) (b: A -> B) (c: B),
  let x := a in (b x = c) ->
  (let x := a in b x) = c.
Proof. intros. simpl. subst x. assumption. Qed.

Lemma decode_encode: forall (inst: Instruction) (z: Z),
    respects_bounds 64 inst ->
    encode inst = z ->
    decode RV64IMA z = inst.
Proof.
  intros.
  let d := eval cbv delta [decode] in decode in change decode with d.
  cbv beta.
  repeat match goal with
  | |- (let x := ?a in ?b) = ?c => cut (let x := a in (b = c));
       [apply (pull_let a (fun x => b) c) | intro]
  end.
  repeat match goal with
  | x := ?t : ?T |- _ => assert (x = t) by (subst x; reflexivity); clearbody x
  end.
  unfold encode in *. repeat autounfold with mappers in *.
  destruct inst;  [destruct i..|subst; exfalso; assumption];
  try reflexivity;
  try (time (
  simpl in H;
  invert_encode;
  try (exfalso; assumption);
  repeat match goal with
         | H: _ /\ _ |- _ =>
           let E := fresh "E" in
           destruct H as [E H];
           rewrite <- E in *;
           clear E;
           try (rewrite <- H in *; clear H)
  end;
  subst;
  repeat lazymatch goal with
         | |- context [if (?x && ?y) then ?a else ?b] =>
           (replace (x && y) with false by (symmetry; prove_andb_false)) ||
           (replace (x && y) with true  by (symmetry; prove_andb_true))
         end;
  (reflexivity || (idtac "Failed to solve:"; match goal with
                   | |- ?G => idtac G
                   end))
  )).
  all: solve [exfalso; assumption].
Time Qed.
