(* Default settings (from HsToCoq.Coq.Preamble) *)

Generalizable All Variables.

Unset Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Coq.Program.Tactics.
Require Coq.Program.Wf.

(* Preamble *)

Require Import Coq.ZArith.BinInt.
Local Open Scope Z.
Require Import riscv.Utility.Utility.
Local Open Scope alu_scope.

(* Converted imports: *)

Require Import Coq.ZArith.BinInt.
Require Utility.Utility.

(* Converted type declarations: *)

Inductive CSR : Type :=
  | MHartID : CSR
  | MISA : CSR
  | MStatus : CSR
  | MTVec : CSR
  | MEDeleg : CSR
  | MIDeleg : CSR
  | MIP : CSR
  | MIE : CSR
  | MCycle : CSR
  | MInstRet : CSR
  | MCounterEn : CSR
  | MScratch : CSR
  | MEPC : CSR
  | MCause : CSR
  | MTVal : CSR
  | MHPMCounter3 : CSR
  | MHPMCounter4 : CSR
  | MHPMCounter5 : CSR
  | MHPMCounter6 : CSR
  | MHPMCounter7 : CSR
  | MHPMCounter8 : CSR
  | MHPMCounter9 : CSR
  | MHPMCounter10 : CSR
  | MHPMCounter11 : CSR
  | MHPMCounter12 : CSR
  | MHPMCounter13 : CSR
  | MHPMCounter14 : CSR
  | MHPMCounter15 : CSR
  | MHPMCounter16 : CSR
  | MHPMCounter17 : CSR
  | MHPMCounter18 : CSR
  | MHPMCounter19 : CSR
  | MHPMCounter20 : CSR
  | MHPMCounter21 : CSR
  | MHPMCounter22 : CSR
  | MHPMCounter23 : CSR
  | MHPMCounter24 : CSR
  | MHPMCounter25 : CSR
  | MHPMCounter26 : CSR
  | MHPMCounter27 : CSR
  | MHPMCounter28 : CSR
  | MHPMCounter29 : CSR
  | MHPMCounter30 : CSR
  | MHPMCounter31 : CSR
  | SStatus : CSR
  | SEDeleg : CSR
  | SIDeleg : CSR
  | STVec : CSR
  | SIP : CSR
  | SIE : CSR
  | SCounterEn : CSR
  | SScratch : CSR
  | SEPC : CSR
  | SCause : CSR
  | STVal : CSR
  | SATP : CSR
  | UStatus : CSR
  | UIE : CSR
  | UTVec : CSR
  | UScratch : CSR
  | UEPC : CSR
  | UCause : CSR
  | UTVal : CSR
  | UIP : CSR
  | FFlags : CSR
  | FRM : CSR
  | FCSR : CSR
  | Time : CSR
  | Cycle : CSR
  | InstRet : CSR
  | InvalidCSR : CSR.

(* Converted value declarations: *)

(* Skipping instance `Spec.CSR.Eq___CSR' of class `GHC.Base.Eq_' *)

Definition lookupCSR : Utility.Utility.MachineInt -> CSR :=
  fun x =>
    if Z.eqb x 768 : bool then MStatus else
    if Z.eqb x 769 : bool then MISA else
    if Z.eqb x 770 : bool then MEDeleg else
    if Z.eqb x 771 : bool then MIDeleg else
    if Z.eqb x 772 : bool then MIE else
    if Z.eqb x 773 : bool then MTVec else
    if Z.eqb x 774 : bool then MCounterEn else
    if Z.eqb x 832 : bool then MScratch else
    if Z.eqb x 833 : bool then MEPC else
    if Z.eqb x 834 : bool then MCause else
    if Z.eqb x 835 : bool then MTVal else
    if Z.eqb x 836 : bool then MIP else
    if Z.eqb x 2816 : bool then MCycle else
    if Z.eqb x 2818 : bool then MInstRet else
    if Z.eqb x 2819 : bool then MHPMCounter3 else
    if Z.eqb x 2820 : bool then MHPMCounter4 else
    if Z.eqb x 2821 : bool then MHPMCounter5 else
    if Z.eqb x 2822 : bool then MHPMCounter6 else
    if Z.eqb x 2823 : bool then MHPMCounter7 else
    if Z.eqb x 2824 : bool then MHPMCounter8 else
    if Z.eqb x 2825 : bool then MHPMCounter9 else
    if Z.eqb x 2826 : bool then MHPMCounter10 else
    if Z.eqb x 2827 : bool then MHPMCounter11 else
    if Z.eqb x 2828 : bool then MHPMCounter12 else
    if Z.eqb x 2829 : bool then MHPMCounter13 else
    if Z.eqb x 2830 : bool then MHPMCounter14 else
    if Z.eqb x 2831 : bool then MHPMCounter15 else
    if Z.eqb x 2832 : bool then MHPMCounter16 else
    if Z.eqb x 2833 : bool then MHPMCounter17 else
    if Z.eqb x 2834 : bool then MHPMCounter18 else
    if Z.eqb x 2835 : bool then MHPMCounter19 else
    if Z.eqb x 2836 : bool then MHPMCounter20 else
    if Z.eqb x 2837 : bool then MHPMCounter21 else
    if Z.eqb x 2838 : bool then MHPMCounter22 else
    if Z.eqb x 2839 : bool then MHPMCounter23 else
    if Z.eqb x 2840 : bool then MHPMCounter24 else
    if Z.eqb x 2841 : bool then MHPMCounter25 else
    if Z.eqb x 2842 : bool then MHPMCounter26 else
    if Z.eqb x 2843 : bool then MHPMCounter27 else
    if Z.eqb x 2844 : bool then MHPMCounter28 else
    if Z.eqb x 2845 : bool then MHPMCounter29 else
    if Z.eqb x 2846 : bool then MHPMCounter30 else
    if Z.eqb x 2847 : bool then MHPMCounter31 else
    if Z.eqb x 256 : bool then SStatus else
    if Z.eqb x 258 : bool then SEDeleg else
    if Z.eqb x 259 : bool then SIDeleg else
    if Z.eqb x 260 : bool then SIE else
    if Z.eqb x 261 : bool then STVec else
    if Z.eqb x 262 : bool then SCounterEn else
    if Z.eqb x 320 : bool then SScratch else
    if Z.eqb x 321 : bool then SEPC else
    if Z.eqb x 322 : bool then SCause else
    if Z.eqb x 323 : bool then STVal else
    if Z.eqb x 324 : bool then SIP else
    if Z.eqb x 384 : bool then SATP else
    if Z.eqb x 0 : bool then UStatus else
    if Z.eqb x 1 : bool then FFlags else
    if Z.eqb x 2 : bool then FRM else
    if Z.eqb x 3 : bool then FCSR else
    if Z.eqb x 4 : bool then UIE else
    if Z.eqb x 5 : bool then UTVec else
    if Z.eqb x 64 : bool then UScratch else
    if Z.eqb x 65 : bool then UEPC else
    if Z.eqb x 66 : bool then UCause else
    if Z.eqb x 67 : bool then UTVal else
    if Z.eqb x 68 : bool then UIP else
    if Z.eqb x 3072 : bool then Cycle else
    if Z.eqb x 3073 : bool then Time else
    if Z.eqb x 3074 : bool then InstRet else
    if Z.eqb x 3860 : bool then MHartID else
    InvalidCSR.

(* External variables:
     Z.eqb bool Utility.Utility.MachineInt
*)
