Require Export Coq.ZArith.ZArith.
Require Export Coq.Lists.List. Import ListNotations.
Require Import coqutil.Tactics.rdelta.
Require Import coqutil.Tactics.destr.
Require Import coqutil.Z.prove_Zeq_bitwise.
Require Import coqutil.Tactics.Tactics.
Require Import coqutil.Tactics.fwd.
Require Export riscv.Spec.Decode.
Require Export riscv.Utility.Encode.
Require Export riscv.Utility.Utility.
Require Import riscv.Proofs.DecodeByExtension.

Local Open Scope Z_scope.

Ltac isConst x :=
  lazymatch x with
  | ?a ^ ?b => isConst a; isConst b
  | ?a - ?b => isConst a; isConst b
  | - ?a => isConst a
  | Z.max ?a ?b => isConst a; isConst b
  | _ => let x' := rdelta x in
         lazymatch isZcst x' with
         | true => idtac
         end
  end.

Lemma verify_decode: forall iset inst,
    supportsF iset = false ->
    verify (decode iset inst) iset \/ decode iset inst = InvalidInstruction inst.
Proof.
  intros. rewrite <- decode_seq_correct.
  assert (bitwidth iset = 2 ^ 5 \/ bitwidth iset = 2 ^ 6) as bw_cases. {
    destruct iset; cbn; auto.
  }
  assert (bitSlice inst 25 26 = 0 -> bitSlice inst 20 26 < bitwidth iset). {
    intros.
    rewrite bitSlice_alt in *. 2-3: cbv; intuition congruence.
    unfold bitSlice' in *.
    Z.div_mod_to_equations.
    Lia.lia.
  }
  assert (signExtend 32 (BinInt.Z.shiftl (bitSlice inst 12 32) 12) mod 2 ^ 12 = 0). {
    unfold signExtend.
    rewrite Z.shiftl_mul_pow2 by (cbv; discriminate 1).
    Z.div_mod_to_equations.
    Lia.lia.
  }
  assert (signExtend 13
   (Z.shiftl (bitSlice inst 31 32) 12 <|> BinInt.Z.shiftl (bitSlice inst 25 31) 5 <|>
    Z.shiftl (bitSlice inst 8 12) 1 <|> BinInt.Z.shiftl (bitSlice inst 7 8) 11) mod 2 = 0). {
    eapply mod20_bitSlice.
    prove_Zeq_bitwise.
  }
  assert (signExtend 21
   (BinInt.Z.shiftl (bitSlice inst 31 32) 20 <|> BinInt.Z.shiftl (bitSlice inst 21 31) 1 <|>
    BinInt.Z.shiftl (bitSlice inst 20 21) 11 <|> BinInt.Z.shiftl (bitSlice inst 12 20) 12)
   mod 2 = 0). {
    eapply mod20_bitSlice.
    prove_Zeq_bitwise.
  }
  unfold decode_seq.
  repeat destruct_one_match; fwd.
  all: (right; reflexivity) || left.
  all: try match goal with
           | H': supportsF _ = true |- _ => exfalso; congruence
           end.
  all: unfold verify, verify_iset.
  all: split;
    [|repeat match goal with
             | H: bitwidth _ = _ |- _ => unfold bitwidth in H
             end;
      unfold supportsM, supportsA, supportsF in *;
      destruct iset; try intuition congruence].
  all: match goal with
       | |- respects_bounds _ (_ ?d) => remember d as r in *; revert dependent r; intro r
       end.
  all: cbv beta zeta delta [decodeI decodeM decodeA decodeF
                            decodeI64 decodeM64 decodeA64 decodeF64
                            decodeCSR
                            isValidI isValidM isValidA isValidF
                            isValidI64 isValidM64 isValidA64 isValidF64
                            isValidCSR].
  all: loop INil.
  all: intros; subst.
  all: match goal with
       | H: ?x = ?x |- _ => clear H
       | H: false = true |- _ => discriminate H
       end.
  all: cbv beta iota zeta delta [respects_bounds apply_InstructionMapper Verifier
         map_Invalid map_R map_R_atomic map_I map_I_shift_57 map_I_shift_66
         map_I_system map_S map_SB map_U map_UJ map_Fence map_FenceI
         verify_Invalid verify_R verify_R_atomic verify_I verify_I_shift_57 verify_I_shift_66
         verify_I_system verify_S verify_SB verify_U verify_UJ verify_Fence verify_FenceI
         machineIntToShamt id
       ].
  all: repeat match goal with
              | |- 0 <= bitSlice _ _ _ < _ => eapply bitSlice_bounds
              | |- _ <= signExtend _ _ < _ => eapply signExtend_bounds; cbv; discriminate 1
              | |- _ /\ _ => split
              | |- ?x <= ?y => isConst x; isConst y; cbv; discriminate 1
              | |- ?x < ?y => isConst x; isConst y; reflexivity
              | |- 0 <= bitSlice _ _ _ => eapply bitSlice_nonneg
              | |- bitSlice _ _ _ < 2 ^ _ => eapply bitSlice_upper_bound
              | |- _ < bitwidth ?iset => replace (bitwidth iset) with 64;
                                         [ change 64 with (2 ^ 6) ]
              | |- _ => auto 3
              end.
Qed.
