Require Export Coq.ZArith.ZArith.
Require Export Coq.Lists.List. Import ListNotations.
Require Import coqutil.Tactics.Tactics.
Require Import coqutil.Tactics.rdelta.
Require Import coqutil.Tactics.destr.
Require Export riscv.Spec.Decode.
Require Export riscv.Utility.Utility.

Ltac pose_lets_of_term t :=
  lazymatch t with
  | let x := ?a in @?b x =>
      pose (x := a);
      let b' := eval cbv beta in (b x) in
      pose_lets_of_term b'
  | _ => idtac
  end.

Ltac return_last_let t :=
  lazymatch t with
  | let _ := _ in let _ := _ in _ =>
      lazymatch t with
      | let x := ?a in @?b x => constr:(
         let x := a in ltac:(
           let b' := eval cbv beta in (b x) in
           let r := return_last_let b' in
           exact r))
      end
  | let x := ?a in ?notALetIn => constr:(a)
  end.

Ltac extract_let t funForNameAndType :=
  lazymatch funForNameAndType with
  | fun name: ?T => name =>
      let s := constr:(ltac:(
        econstructor;
        pose_lets_of_term t;
        clear -name;
        match goal with
        | |- ?G =>
            repeat match goal with
              | y := _ |- _ => revert y
              end;
            pattern G
        end;
        match goal with
        | |- (fun x => @?b x) (let _ := ?e in True) =>
            let r := eval cbv beta in (b True) in
            let t := return_last_let r in unify e t
        end;
        exact I
      ): { res: T | let _ := res in True }) in
      lazymatch s with
      | exist _ ?res _ => exact res
      end
  end.

Tactic Notation "extract_let_of_decode" ident(x) :=
  match goal with
  | bw: Z, inst: Z |- ?T =>
      let t := match eval cbv beta delta [decode] in (decode RV64IMAF inst) with
               | context C[bitwidth RV64IMAF] => let r := context C[bw] in r
               end in
      extract_let t (fun x: T => x)
  end.

Definition decodeI(bw: Z)(inst: Z): InstructionI.
  extract_let_of_decode decodeI.
Defined.

Definition decodeM(bw: Z)(inst: Z): InstructionM.
  extract_let_of_decode decodeM.
Defined.

Definition decodeA(bw: Z)(inst: Z): InstructionA.
  extract_let_of_decode decodeA.
Defined.

Definition decodeF(bw: Z)(inst: Z): InstructionF.
  extract_let_of_decode decodeF.
Defined.

Definition decodeI64(bw: Z)(inst: Z): InstructionI64.
  extract_let_of_decode decodeI64.
Defined.

Definition decodeM64(bw: Z)(inst: Z): InstructionM64.
  extract_let_of_decode decodeM64.
Defined.

Definition decodeA64(bw: Z)(inst: Z): InstructionA64.
  extract_let_of_decode decodeA64.
Defined.

Definition decodeF64(bw: Z)(inst: Z): InstructionF64.
  extract_let_of_decode decodeF64.
Defined.

Definition decodeCSR(bw: Z)(inst: Z): InstructionCSR.
  extract_let_of_decode decodeCSR.
Defined.

Definition decode_resultI(bw: Z)(inst: Z): list Instruction :=
  let r := decodeI bw inst in if isValidI r then [IInstruction r] else [].

Definition decode_resultM(bw: Z)(inst: Z): list Instruction :=
  let r := decodeM bw inst in if isValidM r then [MInstruction r] else [].

Definition decode_resultA(bw: Z)(inst: Z): list Instruction :=
  let r := decodeA bw inst in if isValidA r then [AInstruction r] else [].

Definition decode_resultF(bw: Z)(inst: Z): list Instruction :=
  let r := decodeF bw inst in if isValidF r then [FInstruction r] else [].

Definition decode_resultI64(bw: Z)(inst: Z): list Instruction :=
  let r := decodeI64 bw inst in if isValidI64 r then [I64Instruction r] else [].

Definition decode_resultM64(bw: Z)(inst: Z): list Instruction :=
  let r := decodeM64 bw inst in if isValidM64 r then [M64Instruction r] else [].

Definition decode_resultA64(bw: Z)(inst: Z): list Instruction :=
  let r := decodeA64 bw inst in if isValidA64 r then [A64Instruction r] else [].

Definition decode_resultF64(bw: Z)(inst: Z): list Instruction :=
  let r := decodeF64 bw inst in if isValidF64 r then [F64Instruction r] else [].

Definition decode_resultCSR(bw: Z)(inst: Z): list Instruction :=
  let r := decodeCSR bw inst in if isValidCSR r then [CSRInstruction r] else [].

Definition decode_results(iset: InstructionSet)(inst: Z): list Instruction :=
  (decode_resultI (bitwidth iset) inst) ++
  (if supportsM iset
   then (decode_resultM (bitwidth iset) inst) else []) ++
  (if supportsA iset
   then (decode_resultA (bitwidth iset) inst) else []) ++
  (if supportsF iset
   then (decode_resultF (bitwidth iset) inst) else []) ++
  (if Z.eqb (bitwidth iset) 64
   then (decode_resultI64 (bitwidth iset) inst) else []) ++
  (if andb (Z.eqb (bitwidth iset) 64) (supportsM iset)
   then (decode_resultM64 (bitwidth iset) inst) else []) ++
  (if andb (Z.eqb (bitwidth iset) 64) (supportsA iset)
   then (decode_resultA64 (bitwidth iset) inst) else []) ++
  (if andb (Z.eqb (bitwidth iset) 64) (supportsF iset)
   then (decode_resultF64 (bitwidth iset) inst) else []) ++
  (decode_resultCSR (bitwidth iset) inst).

Definition convertible_decode(iset: InstructionSet)(inst: Z): Instruction :=
  let results := decode_results iset inst in
  if Z.gtb (Z.of_nat (length results)) 1
  then InvalidInstruction inst
  else nth 0 results (InvalidInstruction inst).

Lemma convertible_decode_correct: forall iset inst,
    convertible_decode iset inst = decode iset inst.
Proof. intros. reflexivity. Qed.

Definition decode_alt(iset: InstructionSet)(inst: Z): Instruction :=
  nth 0 (decode_results iset inst) (InvalidInstruction inst).

Lemma push_fun_into_if_branches{A B: Type}(f: A -> B)(a1 a2: A)(c: bool):
  f (if c then a1 else a2) = if c then (f a1) else (f a2).
Proof. destruct c; reflexivity. Qed.

Lemma push_fun_into_if_branches_step{A B: Type}(f: A -> B)(a1 a2: A)(c: bool)(r: B):
  f a2 = r ->
  f (if c then a1 else a2) = (if c then f a1 else r).
Proof. destruct c; congruence. Qed.

Ltac head t :=
  lazymatch t with
  | ?f _ => head f
  | _ => t
  end.

Inductive indent :=
| INil
| ICons(tail: indent).

Notation "" := INil (only printing).
Notation ">> x" := (ICons x)
  (at level 0, right associativity, format ">> x", only printing).

Ltac isnatcst_addition t :=
  lazymatch isnatcst t with
  | true => idtac
  | false => lazymatch t with
             | Nat.add ?a ?b => isnatcst_addition a; isnatcst_addition b
             | _ => fail "Term" t "is not a nat const addition"
             end
  end.

Ltac loop ind :=
  try match goal with
  | |- _ => progress cbn [andb orb] in *; loop ind
  | |- context[Z.eqb ?l ?r] =>
      let r' := rdelta r in
      lazymatch isZcst r' with
      | true => idtac
      end;
      (*idtac ind l r;*)
      let E := fresh "E" in
      destruct (Decidable.Z.eqb_spec l r) as [E | E];
      [ repeat match goal with
               | |- context[Z.eqb l ?r'] =>
                   replace (Z.eqb l r') with false in * by (rewrite E; reflexivity)
               end
      | ];
      loop (ICons ind)
  end.

Lemma extensions_disjoint': forall iset inst,
  (if isValidI (decodeI (bitwidth iset) inst) then 1 else 0) +
  (if isValidM (decodeM (bitwidth iset) inst) then 1 else 0) +
  (if isValidA (decodeA (bitwidth iset) inst) then 1 else 0) +
  (if isValidF (decodeF (bitwidth iset) inst) then 1 else 0) +
  (if isValidI64 (decodeI64 (bitwidth iset) inst) then 1 else 0) +
  (if isValidM64 (decodeM64 (bitwidth iset) inst) then 1 else 0) +
  (if isValidA64 (decodeA64 (bitwidth iset) inst) then 1 else 0) +
  (if isValidF64 (decodeF64 (bitwidth iset) inst) then 1 else 0) +
  (if isValidCSR (decodeCSR (bitwidth iset) inst) then 1 else 0) <= 1.
Proof.
  intros.
  cbv beta zeta delta [decodeI decodeM decodeA decodeF
                       decodeI64 decodeM64 decodeA64 decodeF64
                       decodeCSR
                       isValidI isValidM isValidA isValidF
                       isValidI64 isValidM64 isValidA64 isValidF64
                       isValidCSR].
  loop INil.
  all: match goal with
       | |- ?lhs <= 1 => isnatcst_addition lhs; (apply Nat.le_refl || apply Nat.le_0_1)
       end.
Time Qed. (* 367.474 secs (laptop) *)

Lemma extensions_disjoint: forall iset inst, length (decode_results iset inst) <= 1.
Proof.
  intros.
  cbv beta delta [decode_results].
  rewrite ?List.app_length.
  rewrite ?(push_fun_into_if_branches (@length Instruction)).
  change (length nil) with O.
  rewrite ?Nat.add_assoc.
  repeat match goal with
         | |- ?LHS <= 1 =>
             match LHS with
             |  context C[if ?c then ?a else 0] =>
                  let r := context C[a] in
                  transitivity r;
                  [ destruct c; Lia.lia |]
             end
         end.
  cbv beta delta [decode_resultI decode_resultM decode_resultA decode_resultF
                  decode_resultI64 decode_resultM64 decode_resultA64 decode_resultF64
                  decode_resultCSR].
  cbv zeta.
  rewrite ?(push_fun_into_if_branches (@length Instruction)).
  change (length nil) with O.
  change (length [_]) with 1.
  eapply extensions_disjoint'.
Qed.

Lemma decode_alt_correct: forall iset inst, decode_alt iset inst = decode iset inst.
Proof.
  intros.
  rewrite <- convertible_decode_correct.
  unfold decode_alt, convertible_decode.
  destr (Z.gtb (Z.of_nat (length (decode_results iset inst))) 1). 2: reflexivity.
  exfalso.
  pose proof (extensions_disjoint iset inst).
  Lia.lia.
Qed.

Local Open Scope bool_scope.
Local Open Scope Z_scope.

Definition decode_seq(iset: InstructionSet)(inst: Z): Instruction :=
  let bw := bitwidth iset in
  if isValidI (decodeI bw inst)
  then IInstruction (decodeI bw inst)
  else if supportsM iset && isValidM (decodeM bw inst)
  then MInstruction (decodeM bw inst)
  else if supportsA iset && isValidA (decodeA bw inst)
  then AInstruction (decodeA bw inst)
  else if supportsF iset && isValidF (decodeF bw inst)
  then FInstruction (decodeF bw inst)
  else if (bw =? 64) && isValidI64 (decodeI64 bw inst)
  then I64Instruction (decodeI64 bw inst)
  else if (bw =? 64) && supportsM iset && isValidM64 (decodeM64 bw inst)
  then M64Instruction (decodeM64 bw inst)
  else if (bw =? 64) && supportsA iset && isValidA64 (decodeA64 bw inst)
  then A64Instruction (decodeA64 bw inst)
  else if (bw =? 64) && supportsF iset && isValidF64 (decodeF64 bw inst)
  then F64Instruction (decodeF64 bw inst)
  else if isValidCSR (decodeCSR bw inst)
  then CSRInstruction (decodeCSR bw inst)
  else InvalidInstruction inst.

Lemma double_if_to_andb{T: Type}: forall (c1 c2: bool) (a b: T),
    (if c1 then (if c2 then a else b) else b) = (if andb c1 c2 then a else b).
Proof. destruct c1, c2; reflexivity. Qed.

Lemma decode_seq_correct: forall iset inst,
    decode_seq iset inst = decode iset inst.
Proof.
  intros.
  rewrite <- decode_alt_correct.
  unfold decode_alt, decode_seq, decode_results.
  cbv beta zeta delta [decode_resultI decode_resultM decode_resultA decode_resultF
                       decode_resultI64 decode_resultM64 decode_resultA64 decode_resultF64
                       decode_resultCSR].
  rewrite ?double_if_to_andb.
  repeat (destruct_one_match; cbn [List.app]; [reflexivity|]).
  reflexivity.
Qed.
