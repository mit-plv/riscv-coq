Require Import Coq.Lists.List. Import ListNotations.
Require Import Coq.ZArith.BinInt.
Require Import coqutil.Map.Interface.
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


Section Axiomatic.

  Class AxiomaticRiscvMMIO`{AxiomaticRiscv (Action := MMIOAction)} := {

    theMMIOAddr: word := (word.of_Z 65524); (* maybe like spike *)

    simple_isMMIOAddr: word -> bool := word.eqb theMMIOAddr;

    go_loadWord_MMIO: forall initialL (addr: word) (f: w32 -> M unit)
                             (post: RiscvMachine Register MMIOAction -> Prop),
        (* map.get initialL.(getMem) addr = None -> *)
        (* TODO exists vs forall in the 4byte range *)
        Memory.loadWord initialL.(getMem) addr = None ->
        simple_isMMIOAddr addr = true ->
        (forall (inp: w32),
            mcomp_sat
              (f inp)
              (withLogItem ((initialL.(getMem), MMInput, [addr]),
                            (initialL.(getMem), [word.of_Z (LittleEndian.combine 4 inp)]))
                           initialL)
          post) ->
        mcomp_sat (Bind (Program.loadWord addr) f) initialL post;

    go_storeWord_MMIO: forall initialL addr v post (f: unit -> M unit),
        (* map.get initialL.(getMem) addr = None -> *)
        (* TODO exists vs forall in the 4byte range *)
        Memory.loadWord initialL.(getMem) addr = None ->
        simple_isMMIOAddr addr = true ->
        mcomp_sat
          (f tt)
          (withLogItem ((initialL.(getMem),MMOutput,[addr; word.of_Z (LittleEndian.combine 4 v)]),
                        (initialL.(getMem), []))
          initialL) post ->
        mcomp_sat (Bind (Program.storeWord addr v) f) initialL post;

  }.

End Axiomatic.

Arguments AxiomaticRiscvMMIO {W} {RFF} {mem} M {MM} {RVM} {H}.
