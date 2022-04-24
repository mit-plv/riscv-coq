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
Require Import Monads.
Require Spec.CSR.
Require Spec.CSRField.
Require Spec.Machine.
Require Import Utility.
Require Utility.Utility.

(* No type declarations to convert. *)

(* Converted value declarations: *)

Definition getCSR_SStatus {p : Type -> Type} {t : Type}
  `{Spec.Machine.RiscvMachine p t}
   : p Utility.Utility.MachineInt :=
  Bind (Spec.Machine.getCSRField Spec.CSRField.MXR) (fun mxr =>
          Bind (Spec.Machine.getCSRField Spec.CSRField.SUM) (fun sum =>
                  Bind (Spec.Machine.getCSRField Spec.CSRField.SPP) (fun spp =>
                          Bind (Spec.Machine.getCSRField Spec.CSRField.SPIE) (fun spie =>
                                  Bind (Spec.Machine.getCSRField Spec.CSRField.SIE) (fun sie =>
                                          let base :=
                                            (Z.lor (Z.lor (Z.lor (Z.lor (Z.shiftl mxr 19) (Z.shiftl sum 18)) (Z.shiftl
                                                                  spp 8)) (Z.shiftl spie 5)) (Z.shiftl sie 1)) in
                                          Bind Spec.Machine.getXLEN (fun xlen =>
                                                  if Z.gtb xlen 32 : bool
                                                  then Bind (Spec.Machine.getCSRField Spec.CSRField.MXL) (fun mxl =>
                                                               Bind Spec.Machine.getPC (fun vpc =>
                                                                       Return (Z.lor (Z.shiftl mxl 32) base)))
                                                  else Return base)))))).

Definition setCSR_SStatus {p : Type -> Type} {t : Type}
  `{Spec.Machine.RiscvMachine p t}
   : Utility.Utility.MachineInt -> p unit :=
  fun val =>
    Bind (Spec.Machine.setCSRField Spec.CSRField.MXR (Utility.Utility.bitSlice val
                                    19 20)) (fun _ =>
            Bind (Spec.Machine.setCSRField Spec.CSRField.SUM (Utility.Utility.bitSlice val
                                            18 19)) (fun _ =>
                    Bind (Spec.Machine.setCSRField Spec.CSRField.SPP (Utility.Utility.bitSlice val 8
                                                    9)) (fun _ =>
                            Bind (Spec.Machine.setCSRField Spec.CSRField.SPIE (Utility.Utility.bitSlice val
                                                            5 6)) (fun _ =>
                                    Bind (Spec.Machine.setCSRField Spec.CSRField.SIE (Utility.Utility.bitSlice val 1
                                                                    2)) (fun _ =>
                                            Bind getCSR_SStatus (fun _ => Return tt)))))).

Definition getCSR {p : Type -> Type} {t : Type} `{Spec.Machine.RiscvMachine p t}
   : Spec.CSR.CSR -> p Utility.Utility.MachineInt :=
  fun arg_0__ =>
    match arg_0__ with
    | Spec.CSR.MISA =>
        Bind Spec.Machine.getXLEN (fun xlen =>
                Bind (Spec.Machine.getCSRField Spec.CSRField.MXL) (fun mxl =>
                        Bind (Spec.Machine.getCSRField Spec.CSRField.Extensions) (fun ext =>
                                Return (Z.lor (Z.shiftl mxl (Z.sub xlen 2)) ext))))
    | Spec.CSR.MHartID => Return 0
    | Spec.CSR.MStatus =>
        Bind (Spec.Machine.getCSRField Spec.CSRField.TSR) (fun tsr =>
                Bind (Spec.Machine.getCSRField Spec.CSRField.TW) (fun tw =>
                        Bind (Spec.Machine.getCSRField Spec.CSRField.TVM) (fun tvm =>
                                Bind (Spec.Machine.getCSRField Spec.CSRField.MPRV) (fun mprv =>
                                        Bind (Spec.Machine.getCSRField Spec.CSRField.MPP) (fun mpp =>
                                                Bind (Spec.Machine.getCSRField Spec.CSRField.MPIE) (fun mpie =>
                                                        Bind (Spec.Machine.getCSRField Spec.CSRField.MIE) (fun mie =>
                                                                Bind (Spec.Machine.getCSRField Spec.CSRField.MXL)
                                                                     (fun mxl =>
                                                                        Bind getCSR_SStatus (fun sstatus =>
                                                                                Return (Z.lor (Z.lor (Z.lor (Z.lor
                                                                                                             (Z.lor
                                                                                                              (Z.lor
                                                                                                               (Z.lor
                                                                                                                (Z.lor
                                                                                                                 (Z.shiftl
                                                                                                                  tsr
                                                                                                                  22)
                                                                                                                 (Z.shiftl
                                                                                                                  tw
                                                                                                                  21))
                                                                                                                (Z.shiftl
                                                                                                                 tvm
                                                                                                                 20))
                                                                                                               (Z.shiftl
                                                                                                                mprv
                                                                                                                17))
                                                                                                              (Z.shiftl
                                                                                                               mpp 11))
                                                                                                             (Z.shiftl
                                                                                                              mpie 7))
                                                                                                            (Z.shiftl
                                                                                                             mie 3))
                                                                                                     sstatus) (Z.shiftl
                                                                                               mxl 34)))))))))))
    | Spec.CSR.MEDeleg => Spec.Machine.getCSRField Spec.CSRField.MEDeleg
    | Spec.CSR.MIDeleg => Spec.Machine.getCSRField Spec.CSRField.MIDeleg
    | Spec.CSR.SIP =>
        Bind (Spec.Machine.getCSRField Spec.CSRField.SEIP) (fun seip =>
                Bind (Spec.Machine.getCSRField Spec.CSRField.UEIP) (fun ueip =>
                        Bind (Spec.Machine.getCSRField Spec.CSRField.STIP) (fun stip =>
                                Bind (Spec.Machine.getCSRField Spec.CSRField.UTIP) (fun utip =>
                                        Bind (Spec.Machine.getCSRField Spec.CSRField.SSIP) (fun ssip =>
                                                Bind (Spec.Machine.getCSRField Spec.CSRField.USIP) (fun usip =>
                                                        Return (Z.lor (Z.lor (Z.lor (Z.lor (Z.lor usip (Z.shiftl ssip
                                                                                                   1)) (Z.shiftl utip
                                                                                            4)) (Z.shiftl stip 5))
                                                                             (Z.shiftl ueip 8)) (Z.shiftl seip 9))))))))
    | Spec.CSR.SIE =>
        Bind (Spec.Machine.getCSRField Spec.CSRField.SEIE) (fun seie =>
                Bind (Return 0) (fun ueie =>
                        Bind (Spec.Machine.getCSRField Spec.CSRField.STIE) (fun stie =>
                                Bind (Return 0) (fun utie =>
                                        Bind (Spec.Machine.getCSRField Spec.CSRField.SSIE) (fun ssie =>
                                                Bind (Return 0) (fun usie =>
                                                        Return (Z.lor (Z.lor (Z.lor (Z.lor (Z.lor usie (Z.shiftl ssie
                                                                                                   1)) (Z.shiftl utie
                                                                                            4)) (Z.shiftl stie 5))
                                                                             (Z.shiftl ueie 8)) (Z.shiftl seie 9))))))))
    | Spec.CSR.MTVec =>
        Bind (Spec.Machine.getCSRField Spec.CSRField.MTVecBase) (fun base =>
                Bind (Spec.Machine.getCSRField Spec.CSRField.MTVecMode) (fun mode =>
                        Return (Z.lor (Z.shiftl base 2) mode)))
    | Spec.CSR.MCycle => Spec.Machine.getCSRField Spec.CSRField.MCycle
    | Spec.CSR.MInstRet => Spec.Machine.getCSRField Spec.CSRField.MInstRet
    | Spec.CSR.MEPC => Spec.Machine.getCSRField Spec.CSRField.MEPC
    | Spec.CSR.MScratch => Spec.Machine.getCSRField Spec.CSRField.MScratch
    | Spec.CSR.InstRet => Spec.Machine.getCSR_InstRet
    | Spec.CSR.Time => Spec.Machine.getCSR_Time
    | Spec.CSR.Cycle => Spec.Machine.getCSR_Cycle
    | Spec.CSR.MHPMCounter3 => Return (Z.neg 1)
    | Spec.CSR.MHPMCounter4 => Return (Z.neg 1)
    | Spec.CSR.MHPMCounter5 => Return (Z.neg 1)
    | Spec.CSR.MHPMCounter6 => Return (Z.neg 1)
    | Spec.CSR.MHPMCounter7 => Return (Z.neg 1)
    | Spec.CSR.MHPMCounter8 => Return (Z.neg 1)
    | Spec.CSR.MHPMCounter9 => Return (Z.neg 1)
    | Spec.CSR.MHPMCounter10 => Return (Z.neg 1)
    | Spec.CSR.MHPMCounter11 => Return (Z.neg 1)
    | Spec.CSR.MHPMCounter12 => Return (Z.neg 1)
    | Spec.CSR.MHPMCounter13 => Return (Z.neg 1)
    | Spec.CSR.MHPMCounter14 => Return (Z.neg 1)
    | Spec.CSR.MHPMCounter15 => Return (Z.neg 1)
    | Spec.CSR.MHPMCounter16 => Return (Z.neg 1)
    | Spec.CSR.MHPMCounter17 => Return (Z.neg 1)
    | Spec.CSR.MHPMCounter18 => Return (Z.neg 1)
    | Spec.CSR.MHPMCounter19 => Return (Z.neg 1)
    | Spec.CSR.MHPMCounter20 => Return (Z.neg 1)
    | Spec.CSR.MHPMCounter21 => Return (Z.neg 1)
    | Spec.CSR.MHPMCounter22 => Return (Z.neg 1)
    | Spec.CSR.MHPMCounter23 => Return (Z.neg 1)
    | Spec.CSR.MHPMCounter24 => Return (Z.neg 1)
    | Spec.CSR.MHPMCounter25 => Return (Z.neg 1)
    | Spec.CSR.MHPMCounter26 => Return (Z.neg 1)
    | Spec.CSR.MHPMCounter27 => Return (Z.neg 1)
    | Spec.CSR.MHPMCounter28 => Return (Z.neg 1)
    | Spec.CSR.MHPMCounter29 => Return (Z.neg 1)
    | Spec.CSR.MHPMCounter30 => Return (Z.neg 1)
    | Spec.CSR.MHPMCounter31 => Return (Z.neg 1)
    | Spec.CSR.MCounterEn =>
        Bind (Spec.Machine.getCSRField Spec.CSRField.MHPM) (fun mhpm =>
                Bind (Spec.Machine.getCSRField Spec.CSRField.MIR) (fun mir =>
                        Bind (Spec.Machine.getCSRField Spec.CSRField.MTM) (fun mtm =>
                                Bind (Spec.Machine.getCSRField Spec.CSRField.MCY) (fun mcy =>
                                        Return (Z.lor (Z.lor (Z.lor mcy (Z.shiftl mtm 1)) (Z.shiftl mir 2)) (Z.shiftl
                                                       mhpm 3))))))
    | Spec.CSR.MCause =>
        Bind Spec.Machine.getXLEN (fun xlen =>
                Bind (Spec.Machine.getCSRField Spec.CSRField.MCauseCode) (fun code =>
                        Bind (Spec.Machine.getCSRField Spec.CSRField.MCauseInterrupt) (fun interrupt =>
                                Return (Z.lor (Z.shiftl interrupt (Z.sub xlen 1)) code))))
    | Spec.CSR.MTVal => Spec.Machine.getCSRField Spec.CSRField.MTVal
    | Spec.CSR.SStatus => getCSR_SStatus
    | Spec.CSR.STVec =>
        Bind (Spec.Machine.getCSRField Spec.CSRField.STVecBase) (fun base =>
                Bind (Spec.Machine.getCSRField Spec.CSRField.STVecMode) (fun mode =>
                        Return (Z.lor (Z.shiftl base 2) mode)))
    | Spec.CSR.SEPC => Spec.Machine.getCSRField Spec.CSRField.SEPC
    | Spec.CSR.SCounterEn =>
        Bind (Spec.Machine.getCSRField Spec.CSRField.SHPM) (fun shpm =>
                Bind (Spec.Machine.getCSRField Spec.CSRField.SIR) (fun sir =>
                        Bind (Spec.Machine.getCSRField Spec.CSRField.STM) (fun stm =>
                                Bind (Spec.Machine.getCSRField Spec.CSRField.SCY) (fun scy =>
                                        Return (Z.lor (Z.lor (Z.lor scy (Z.shiftl stm 1)) (Z.shiftl sir 2)) (Z.shiftl
                                                       shpm 3))))))
    | Spec.CSR.SScratch => Spec.Machine.getCSRField Spec.CSRField.SScratch
    | Spec.CSR.SCause =>
        Bind Spec.Machine.getXLEN (fun xlen =>
                Bind (Spec.Machine.getCSRField Spec.CSRField.SCauseCode) (fun code =>
                        Bind (Spec.Machine.getCSRField Spec.CSRField.SCauseInterrupt) (fun interrupt =>
                                Return (Z.lor (Z.shiftl interrupt (Z.sub xlen 1)) code))))
    | Spec.CSR.STVal => Spec.Machine.getCSRField Spec.CSRField.STVal
    | Spec.CSR.SATP =>
        Bind (Spec.Machine.getCSRField Spec.CSRField.TVM) (fun tvm =>
                Bind (when (Z.eqb tvm 1) (Spec.Machine.raiseException (ZToReg 0) (ZToReg 2)))
                     (fun _ =>
                        Bind Spec.Machine.getXLEN (fun xlen =>
                                Bind (Spec.Machine.getCSRField Spec.CSRField.MODE) (fun mode =>
                                        Bind (Spec.Machine.getCSRField Spec.CSRField.ASID) (fun asid =>
                                                Bind (Spec.Machine.getCSRField Spec.CSRField.PPN) (fun ppn =>
                                                        if Z.eqb xlen 32 : bool
                                                        then Return (Z.lor (Z.lor (Z.shiftl mode 31) (Z.shiftl asid 22))
                                                                           ppn)
                                                        else Return (Z.lor (Z.lor (Z.shiftl mode 60) (Z.shiftl asid 44))
                                                                           ppn)))))))
    | Spec.CSR.FFlags => Spec.Machine.getCSRField Spec.CSRField.FFlags
    | Spec.CSR.FRM => Spec.Machine.getCSRField Spec.CSRField.FRM
    | Spec.CSR.MIP =>
        Bind (Spec.Machine.getCSRField Spec.CSRField.MEIP) (fun meip =>
                Bind (Spec.Machine.getCSRField Spec.CSRField.SEIP) (fun seip =>
                        Bind (Spec.Machine.getCSRField Spec.CSRField.UEIP) (fun ueip =>
                                Bind (Spec.Machine.getCSRField Spec.CSRField.MTIP) (fun mtip =>
                                        Bind (Spec.Machine.getCSRField Spec.CSRField.STIP) (fun stip =>
                                                Bind (Spec.Machine.getCSRField Spec.CSRField.UTIP) (fun utip =>
                                                        Bind (Spec.Machine.getCSRField Spec.CSRField.MSIP) (fun msip =>
                                                                Bind (Spec.Machine.getCSRField Spec.CSRField.SSIP)
                                                                     (fun ssip =>
                                                                        Bind (Spec.Machine.getCSRField
                                                                              Spec.CSRField.USIP) (fun usip =>
                                                                                Return (Z.lor (Z.lor (Z.lor (Z.lor
                                                                                                             (Z.lor
                                                                                                              (Z.lor
                                                                                                               (Z.lor
                                                                                                                (Z.lor
                                                                                                                 usip
                                                                                                                 (Z.shiftl
                                                                                                                  ssip
                                                                                                                  1))
                                                                                                                (Z.shiftl
                                                                                                                 msip
                                                                                                                 3))
                                                                                                               (Z.shiftl
                                                                                                                utip 4))
                                                                                                              (Z.shiftl
                                                                                                               stip 5))
                                                                                                             (Z.shiftl
                                                                                                              mtip 7))
                                                                                                            (Z.shiftl
                                                                                                             ueip 8))
                                                                                                     (Z.shiftl seip 9))
                                                                                              (Z.shiftl meip
                                                                                               11)))))))))))
    | Spec.CSR.MIE =>
        Bind (Spec.Machine.getCSRField Spec.CSRField.MEIE) (fun meie =>
                Bind (Spec.Machine.getCSRField Spec.CSRField.SEIE) (fun seie =>
                        Bind (Return 0) (fun ueie =>
                                Bind (Spec.Machine.getCSRField Spec.CSRField.MTIE) (fun mtie =>
                                        Bind (Spec.Machine.getCSRField Spec.CSRField.STIE) (fun stie =>
                                                Bind (Return 0) (fun utie =>
                                                        Bind (Spec.Machine.getCSRField Spec.CSRField.MSIE) (fun msie =>
                                                                Bind (Spec.Machine.getCSRField Spec.CSRField.SSIE)
                                                                     (fun ssie =>
                                                                        Bind (Return 0) (fun usie =>
                                                                                Return (Z.lor (Z.lor (Z.lor (Z.lor
                                                                                                             (Z.lor
                                                                                                              (Z.lor
                                                                                                               (Z.lor
                                                                                                                (Z.lor
                                                                                                                 usie
                                                                                                                 (Z.shiftl
                                                                                                                  ssie
                                                                                                                  1))
                                                                                                                (Z.shiftl
                                                                                                                 msie
                                                                                                                 3))
                                                                                                               (Z.shiftl
                                                                                                                utie 4))
                                                                                                              (Z.shiftl
                                                                                                               stie 5))
                                                                                                             (Z.shiftl
                                                                                                              mtie 7))
                                                                                                            (Z.shiftl
                                                                                                             ueie 8))
                                                                                                     (Z.shiftl seie 9))
                                                                                              (Z.shiftl meie
                                                                                               11)))))))))))
    | Spec.CSR.FCSR =>
        Bind (Spec.Machine.getCSRField Spec.CSRField.FFlags) (fun fflags =>
                Bind (Spec.Machine.getCSRField Spec.CSRField.FRM) (fun frm =>
                        Return (Z.lor (Z.shiftl frm 5) fflags)))
    | _ => Return (Z.neg 1)
    end.

Definition setCSR {p : Type -> Type} {t : Type} `{Spec.Machine.RiscvMachine p t}
   : Spec.CSR.CSR -> Utility.Utility.MachineInt -> p unit :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | Spec.CSR.MStatus, val =>
        Bind (setCSR_SStatus val) (fun _ =>
                Bind (Spec.Machine.setCSRField Spec.CSRField.TSR (Utility.Utility.bitSlice val
                                                22 23)) (fun _ =>
                        Bind (Spec.Machine.setCSRField Spec.CSRField.TW (Utility.Utility.bitSlice val 21
                                                        22)) (fun _ =>
                                Bind (Spec.Machine.setCSRField Spec.CSRField.TVM (Utility.Utility.bitSlice val
                                                                20 21)) (fun _ =>
                                        Bind (Spec.Machine.setCSRField Spec.CSRField.MPRV (Utility.Utility.bitSlice val
                                                                        17 18)) (fun _ =>
                                                Bind (Spec.Machine.setCSRField Spec.CSRField.MPP
                                                                               (Utility.Utility.bitSlice val 11 13))
                                                     (fun _ =>
                                                        Bind (Spec.Machine.setCSRField Spec.CSRField.MPIE
                                                                                       (Utility.Utility.bitSlice val 7
                                                                                        8)) (fun _ =>
                                                                Spec.Machine.setCSRField Spec.CSRField.MIE
                                                                                         (Utility.Utility.bitSlice val 3
                                                                                          4))))))))
    | Spec.CSR.MEDeleg, val =>
        Spec.Machine.setCSRField Spec.CSRField.MEDeleg (Z.land val (Z.lnot (Z.shiftl 1
                                                                            11)))
    | Spec.CSR.MIDeleg, val => Spec.Machine.setCSRField Spec.CSRField.MIDeleg val
    | Spec.CSR.SIP, val =>
        let usip := Utility.Utility.bitSlice val 0 1 in
        let ssip := Utility.Utility.bitSlice val 1 2 in
        let utip := Utility.Utility.bitSlice val 4 5 in
        let stip := Utility.Utility.bitSlice val 5 6 in
        let ueip := Utility.Utility.bitSlice val 8 9 in
        let seip := Utility.Utility.bitSlice val 9 10 in
        Bind (Spec.Machine.setCSRField Spec.CSRField.USIP usip) (fun _ =>
                Bind (Spec.Machine.setCSRField Spec.CSRField.SSIP ssip) (fun _ =>
                        Bind (Spec.Machine.setCSRField Spec.CSRField.UTIP utip) (fun _ =>
                                Bind (Spec.Machine.setCSRField Spec.CSRField.STIP stip) (fun _ =>
                                        Bind (Spec.Machine.setCSRField Spec.CSRField.UEIP ueip) (fun _ =>
                                                Spec.Machine.setCSRField Spec.CSRField.SEIP seip)))))
    | Spec.CSR.SIE, val =>
        let usie := Utility.Utility.bitSlice val 0 1 in
        let ssie := Utility.Utility.bitSlice val 1 2 in
        let utie := Utility.Utility.bitSlice val 4 5 in
        let stie := Utility.Utility.bitSlice val 5 6 in
        let ueie := Utility.Utility.bitSlice val 8 9 in
        let seie := Utility.Utility.bitSlice val 9 10 in
        Bind (Spec.Machine.setCSRField Spec.CSRField.SSIE ssie) (fun _ =>
                Bind (Spec.Machine.setCSRField Spec.CSRField.STIE stie) (fun _ =>
                        Spec.Machine.setCSRField Spec.CSRField.SEIE seie))
    | Spec.CSR.MTVec, val =>
        Bind (Spec.Machine.setCSRField Spec.CSRField.MTVecMode (Utility.Utility.bitSlice
                                        val 0 2)) (fun _ =>
                Spec.Machine.setCSRField Spec.CSRField.MTVecBase (Z.shiftl val (Z.neg 2)))
    | Spec.CSR.MEPC, val => Spec.Machine.setCSRField Spec.CSRField.MEPC val
    | Spec.CSR.MCounterEn, val =>
        let mhpm := Z.shiftl val (Z.neg 3) in
        let mir := Utility.Utility.bitSlice val 2 3 in
        let mtm := Utility.Utility.bitSlice val 1 2 in
        let mcy := Utility.Utility.bitSlice val 0 1 in
        Bind (Spec.Machine.setCSRField Spec.CSRField.MHPM mhpm) (fun _ =>
                Bind (Spec.Machine.setCSRField Spec.CSRField.MIR mir) (fun _ =>
                        Bind (Spec.Machine.setCSRField Spec.CSRField.MTM mtm) (fun _ =>
                                Spec.Machine.setCSRField Spec.CSRField.MCY mcy)))
    | Spec.CSR.MScratch, val => Spec.Machine.setCSRField Spec.CSRField.MScratch val
    | Spec.CSR.MCause, val =>
        Bind Spec.Machine.getXLEN (fun xlen =>
                Bind (Spec.Machine.setCSRField Spec.CSRField.MCauseCode
                                               (Utility.Utility.bitSlice val 0 (Z.sub xlen 1))) (fun _ =>
                        Spec.Machine.setCSRField Spec.CSRField.MCauseInterrupt (Utility.Utility.bitSlice
                                                  val (Z.sub xlen 1) xlen)))
    | Spec.CSR.MTVal, val => Spec.Machine.setCSRField Spec.CSRField.MTVal val
    | Spec.CSR.SStatus, val => setCSR_SStatus val
    | Spec.CSR.STVec, val =>
        Bind (Spec.Machine.setCSRField Spec.CSRField.STVecMode (Utility.Utility.bitSlice
                                        val 0 2)) (fun _ =>
                Spec.Machine.setCSRField Spec.CSRField.STVecBase (Z.shiftl val (Z.neg 2)))
    | Spec.CSR.SEPC, val => Spec.Machine.setCSRField Spec.CSRField.SEPC val
    | Spec.CSR.SScratch, val => Spec.Machine.setCSRField Spec.CSRField.SScratch val
    | Spec.CSR.SCounterEn, val =>
        let shpm := Z.shiftl val (Z.neg 3) in
        let sir := Utility.Utility.bitSlice val 2 3 in
        let stm := Utility.Utility.bitSlice val 1 2 in
        let scy := Utility.Utility.bitSlice val 0 1 in
        Bind (Spec.Machine.setCSRField Spec.CSRField.SHPM shpm) (fun _ =>
                Bind (Spec.Machine.setCSRField Spec.CSRField.SIR sir) (fun _ =>
                        Bind (Spec.Machine.setCSRField Spec.CSRField.STM stm) (fun _ =>
                                Spec.Machine.setCSRField Spec.CSRField.SCY scy)))
    | Spec.CSR.SCause, val =>
        Bind Spec.Machine.getXLEN (fun xlen =>
                Bind (Spec.Machine.setCSRField Spec.CSRField.SCauseCode
                                               (Utility.Utility.bitSlice val 0 (Z.sub xlen 1))) (fun _ =>
                        Spec.Machine.setCSRField Spec.CSRField.SCauseInterrupt (Utility.Utility.bitSlice
                                                  val (Z.sub xlen 1) xlen)))
    | Spec.CSR.STVal, val => Spec.Machine.setCSRField Spec.CSRField.STVal val
    | Spec.CSR.MIP, val =>
        let usip := Utility.Utility.bitSlice val 0 1 in
        let ssip := Utility.Utility.bitSlice val 1 2 in
        let msip := Utility.Utility.bitSlice val 3 4 in
        let utip := Utility.Utility.bitSlice val 4 5 in
        let stip := Utility.Utility.bitSlice val 5 6 in
        let mtip := Utility.Utility.bitSlice val 7 8 in
        let ueip := Utility.Utility.bitSlice val 8 9 in
        let seip := Utility.Utility.bitSlice val 9 10 in
        let meip := Utility.Utility.bitSlice val 11 12 in
        Bind (Spec.Machine.setCSRField Spec.CSRField.USIP usip) (fun _ =>
                Bind (Spec.Machine.setCSRField Spec.CSRField.SSIP ssip) (fun _ =>
                        Bind (Spec.Machine.setCSRField Spec.CSRField.MSIP msip) (fun _ =>
                                Bind (Spec.Machine.setCSRField Spec.CSRField.UTIP utip) (fun _ =>
                                        Bind (Spec.Machine.setCSRField Spec.CSRField.STIP stip) (fun _ =>
                                                Bind (Spec.Machine.setCSRField Spec.CSRField.MTIP mtip) (fun _ =>
                                                        Bind (Spec.Machine.setCSRField Spec.CSRField.UEIP ueip)
                                                             (fun _ =>
                                                                Bind (Spec.Machine.setCSRField Spec.CSRField.SEIP seip)
                                                                     (fun _ =>
                                                                        Spec.Machine.setCSRField Spec.CSRField.MEIP
                                                                                                 meip))))))))
    | Spec.CSR.MIE, val =>
        let usie := Utility.Utility.bitSlice val 0 1 in
        let ssie := Utility.Utility.bitSlice val 1 2 in
        let msie := Utility.Utility.bitSlice val 3 4 in
        let utie := Utility.Utility.bitSlice val 4 5 in
        let stie := Utility.Utility.bitSlice val 5 6 in
        let mtie := Utility.Utility.bitSlice val 7 8 in
        let ueie := Utility.Utility.bitSlice val 8 9 in
        let seie := Utility.Utility.bitSlice val 9 10 in
        let meie := Utility.Utility.bitSlice val 11 12 in
        Bind (Spec.Machine.setCSRField Spec.CSRField.SSIE ssie) (fun _ =>
                Bind (Spec.Machine.setCSRField Spec.CSRField.MSIE msie) (fun _ =>
                        Bind (Spec.Machine.setCSRField Spec.CSRField.STIE stie) (fun _ =>
                                Bind (Spec.Machine.setCSRField Spec.CSRField.MTIE mtie) (fun _ =>
                                        Bind (Spec.Machine.setCSRField Spec.CSRField.SEIE seie) (fun _ =>
                                                Spec.Machine.setCSRField Spec.CSRField.MEIE meie)))))
    | Spec.CSR.SATP, val =>
        Bind Spec.Machine.getPrivMode (fun priv =>
                Bind (Spec.Machine.getCSRField Spec.CSRField.TVM) (fun tvm =>
                        Bind (when (andb (Spec.Machine.PrivMode_eqb priv Spec.Machine.Supervisor) (Z.eqb
                                          tvm 1)) (Spec.Machine.raiseException (ZToReg 0) (ZToReg 2))) (fun _ =>
                                Bind Spec.Machine.getXLEN (fun xlen =>
                                        let mode :=
                                          if Z.eqb xlen 32 : bool
                                          then Utility.Utility.bitSlice val 31 32
                                          else Utility.Utility.bitSlice val 60 64 in
                                        when (orb (Z.eqb mode 1) (orb (Z.eqb mode 8) (Z.eqb mode 9))) (if Z.eqb xlen
                                                                                                                32 : bool
                                                                                                       then Bind
                                                                                                            (Spec.Machine.setCSRField
                                                                                                             Spec.CSRField.MODE
                                                                                                             mode)
                                                                                                            (fun _ =>
                                                                                                               Bind
                                                                                                               (Spec.Machine.setCSRField
                                                                                                                Spec.CSRField.ASID
                                                                                                                (Utility.Utility.bitSlice
                                                                                                                 val 22
                                                                                                                 31))
                                                                                                               (fun _ =>
                                                                                                                  Spec.Machine.setCSRField
                                                                                                                  Spec.CSRField.PPN
                                                                                                                  (Utility.Utility.bitSlice
                                                                                                                   val 0
                                                                                                                   22)))
                                                                                                       else Bind
                                                                                                            (Spec.Machine.setCSRField
                                                                                                             Spec.CSRField.MODE
                                                                                                             mode)
                                                                                                            (fun _ =>
                                                                                                               Bind
                                                                                                               (Spec.Machine.setCSRField
                                                                                                                Spec.CSRField.ASID
                                                                                                                (Utility.Utility.bitSlice
                                                                                                                 val 44
                                                                                                                 60))
                                                                                                               (fun _ =>
                                                                                                                  Spec.Machine.setCSRField
                                                                                                                  Spec.CSRField.PPN
                                                                                                                  (Utility.Utility.bitSlice
                                                                                                                   val 0
                                                                                                                   44))))))))
    | Spec.CSR.FFlags, val =>
        Spec.Machine.setCSRField Spec.CSRField.FFlags (Utility.Utility.bitSlice val 0 5)
    | Spec.CSR.FRM, val =>
        Spec.Machine.setCSRField Spec.CSRField.FRM (Utility.Utility.bitSlice val 0 3)
    | Spec.CSR.FCSR, val =>
        Bind (Spec.Machine.setCSRField Spec.CSRField.FFlags (Utility.Utility.bitSlice
                                        val 0 5)) (fun _ =>
                Spec.Machine.setCSRField Spec.CSRField.FRM (Utility.Utility.bitSlice val 5 8))
    | _, _ => Return tt
    end.

(* External variables:
     Bind Return Type Z.eqb Z.gtb Z.land Z.lnot Z.lor Z.neg Z.shiftl Z.sub ZToReg
     andb bool orb tt unit when Spec.CSR.CSR Spec.CSR.Cycle Spec.CSR.FCSR
     Spec.CSR.FFlags Spec.CSR.FRM Spec.CSR.InstRet Spec.CSR.MCause
     Spec.CSR.MCounterEn Spec.CSR.MCycle Spec.CSR.MEDeleg Spec.CSR.MEPC
     Spec.CSR.MHPMCounter10 Spec.CSR.MHPMCounter11 Spec.CSR.MHPMCounter12
     Spec.CSR.MHPMCounter13 Spec.CSR.MHPMCounter14 Spec.CSR.MHPMCounter15
     Spec.CSR.MHPMCounter16 Spec.CSR.MHPMCounter17 Spec.CSR.MHPMCounter18
     Spec.CSR.MHPMCounter19 Spec.CSR.MHPMCounter20 Spec.CSR.MHPMCounter21
     Spec.CSR.MHPMCounter22 Spec.CSR.MHPMCounter23 Spec.CSR.MHPMCounter24
     Spec.CSR.MHPMCounter25 Spec.CSR.MHPMCounter26 Spec.CSR.MHPMCounter27
     Spec.CSR.MHPMCounter28 Spec.CSR.MHPMCounter29 Spec.CSR.MHPMCounter3
     Spec.CSR.MHPMCounter30 Spec.CSR.MHPMCounter31 Spec.CSR.MHPMCounter4
     Spec.CSR.MHPMCounter5 Spec.CSR.MHPMCounter6 Spec.CSR.MHPMCounter7
     Spec.CSR.MHPMCounter8 Spec.CSR.MHPMCounter9 Spec.CSR.MHartID Spec.CSR.MIDeleg
     Spec.CSR.MIE Spec.CSR.MIP Spec.CSR.MISA Spec.CSR.MInstRet Spec.CSR.MScratch
     Spec.CSR.MStatus Spec.CSR.MTVal Spec.CSR.MTVec Spec.CSR.SATP Spec.CSR.SCause
     Spec.CSR.SCounterEn Spec.CSR.SEPC Spec.CSR.SIE Spec.CSR.SIP Spec.CSR.SScratch
     Spec.CSR.SStatus Spec.CSR.STVal Spec.CSR.STVec Spec.CSR.Time Spec.CSRField.ASID
     Spec.CSRField.Extensions Spec.CSRField.FFlags Spec.CSRField.FRM
     Spec.CSRField.MCY Spec.CSRField.MCauseCode Spec.CSRField.MCauseInterrupt
     Spec.CSRField.MCycle Spec.CSRField.MEDeleg Spec.CSRField.MEIE Spec.CSRField.MEIP
     Spec.CSRField.MEPC Spec.CSRField.MHPM Spec.CSRField.MIDeleg Spec.CSRField.MIE
     Spec.CSRField.MIR Spec.CSRField.MInstRet Spec.CSRField.MODE Spec.CSRField.MPIE
     Spec.CSRField.MPP Spec.CSRField.MPRV Spec.CSRField.MSIE Spec.CSRField.MSIP
     Spec.CSRField.MScratch Spec.CSRField.MTIE Spec.CSRField.MTIP Spec.CSRField.MTM
     Spec.CSRField.MTVal Spec.CSRField.MTVecBase Spec.CSRField.MTVecMode
     Spec.CSRField.MXL Spec.CSRField.MXR Spec.CSRField.PPN Spec.CSRField.SCY
     Spec.CSRField.SCauseCode Spec.CSRField.SCauseInterrupt Spec.CSRField.SEIE
     Spec.CSRField.SEIP Spec.CSRField.SEPC Spec.CSRField.SHPM Spec.CSRField.SIE
     Spec.CSRField.SIR Spec.CSRField.SPIE Spec.CSRField.SPP Spec.CSRField.SSIE
     Spec.CSRField.SSIP Spec.CSRField.SScratch Spec.CSRField.STIE Spec.CSRField.STIP
     Spec.CSRField.STM Spec.CSRField.STVal Spec.CSRField.STVecBase
     Spec.CSRField.STVecMode Spec.CSRField.SUM Spec.CSRField.TSR Spec.CSRField.TVM
     Spec.CSRField.TW Spec.CSRField.UEIP Spec.CSRField.USIP Spec.CSRField.UTIP
     Spec.Machine.PrivMode_eqb Spec.Machine.RiscvMachine Spec.Machine.Supervisor
     Spec.Machine.getCSRField Spec.Machine.getCSR_Cycle Spec.Machine.getCSR_InstRet
     Spec.Machine.getCSR_Time Spec.Machine.getPC Spec.Machine.getPrivMode
     Spec.Machine.getXLEN Spec.Machine.raiseException Spec.Machine.setCSRField
     Utility.Utility.MachineInt Utility.Utility.bitSlice
*)
