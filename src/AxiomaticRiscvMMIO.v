Require Import Coq.Lists.List. Import ListNotations.
Require Import Coq.ZArith.BinInt.
Require Import coqutil.Map.Interface.
Require Import coqutil.Datatypes.HList.
Require Import riscv.util.Monads.
Require Import riscv.Utility.
Require Import riscv.Decode.
Require Import riscv.Memory.
Require Import riscv.Program.
Require Import riscv.RiscvMachine.
Require Import riscv.MkMachineWidth.
Require Export riscv.AxiomaticRiscv.
Require Import riscv.MMIOTrace.
Require Import coqutil.Word.LittleEndian.

Definition Nones{A: Type}(n: nat): tuple (option A) n := tuple.unfoldn (fun _ => None) n None.

Section Axiomatic.

  Class AxiomaticRiscvMMIO`{AxiomaticRiscv (Action := MMIOAction)} := {

    go_loadWord_MMIO: forall initialL (addr: word) (f: w32 -> M unit)
                             (post: RiscvMachine Register MMIOAction -> Prop),
        map.getmany_of_tuple initialL.(getMem) (footprint addr 4) = Some (Nones 4) ->
        (forall (inp: w32),
            mcomp_sat
              (f inp)
              (withLogItem ((initialL.(getMem), MMInput, [addr]),
                            (initialL.(getMem), [word.of_Z (LittleEndian.combine 4 inp)]))
                           initialL)
          post) ->
        mcomp_sat (Bind (Program.loadWord addr) f) initialL post;

    go_storeWord_MMIO: forall initialL addr v post (f: unit -> M unit),
        map.getmany_of_tuple initialL.(getMem) (footprint addr 4) = Some (Nones 4) ->
        mcomp_sat
          (f tt)
          (withLogItem ((initialL.(getMem),MMOutput,[addr; word.of_Z (LittleEndian.combine 4 v)]),
                        (initialL.(getMem), []))
          initialL) post ->
        mcomp_sat (Bind (Program.storeWord addr v) f) initialL post;

  }.

End Axiomatic.

Arguments AxiomaticRiscvMMIO {W} {RFF} {mem} M {MM} {RVM} {H}.
