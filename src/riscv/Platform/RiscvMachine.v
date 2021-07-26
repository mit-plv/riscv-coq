Require Import Coq.Strings.String.
Require Import Coq.ZArith.BinInt.
Require Import coqutil.Map.Interface.
Require Import coqutil.Word.Interface.
Require Import coqutil.Word.LittleEndian.
Require Import riscv.Spec.Decode.
Require Import riscv.Platform.Memory.
Require Import riscv.Utility.Utility.


Section Machine.

  Context {width: Z} {word: word width} {word_ok: word.ok word}.
  Context {Registers: map.map Register word}.
  Context {Mem: map.map word byte}.

  (* (memory before call, call name, arg values) and (memory after call, return values) *)
  Definition LogItem{_: Bitwidth width}: Type := (Mem * string * list word) * (Mem * list word).

  (* set of executable addresses. On some processors, this could be the whole address range,
     while on others, only a specific range. And when an address is written, we might
     conservatively remove it from that set if we want to prove that our software does not
     depend on self-modifying code being possible.
     The ifence instruction will flush the instruction cache and therefore put back the
     set of executable addresses to the whole range. *)
  Definition XAddrs: Type := list word.

  Definition isXAddr1B(a: word)(xAddrs: XAddrs): bool :=
    match List.find (word.eqb a) xAddrs with
    | Some _ => true
    | None => false
    end.

  Definition isXAddr4B(a: word)(xAddrs: XAddrs): bool :=
    isXAddr1B a xAddrs &&
    isXAddr1B (word.add a (word.of_Z 1)) xAddrs &&
    isXAddr1B (word.add a (word.of_Z 2)) xAddrs &&
    isXAddr1B (word.add a (word.of_Z 3)) xAddrs.

  Definition isXAddr1: word -> XAddrs -> Prop := @List.In word.

  Definition isXAddr4(a: word)(xAddrs: XAddrs): Prop :=
    isXAddr1 a xAddrs /\
    isXAddr1 (word.add a (word.of_Z 1)) xAddrs /\
    isXAddr1 (word.add a (word.of_Z 2)) xAddrs /\
    isXAddr1 (word.add a (word.of_Z 3)) xAddrs.

  Lemma isXAddr1B_holds: forall a xAddrs,
      isXAddr1B a xAddrs = true -> isXAddr1 a xAddrs.
  Proof.
    unfold isXAddr1B, isXAddr1. intros.
    destruct (List.find (word.eqb a) xAddrs) eqn: E; [|discriminate].
    apply List.find_some in E. destruct E.
    apply Word.Properties.word.eqb_true in H1.
    subst. assumption.
  Qed.

  Lemma isXAddr1B_not: forall a xAddrs,
      isXAddr1B a xAddrs = false -> ~ isXAddr1 a xAddrs.
  Proof.
    unfold isXAddr1B, isXAddr1. intros.
    destruct (List.find (word.eqb a) xAddrs) eqn: E; [discriminate|].
    intro C.
    pose proof (List.find_none _ _ E _ C) as P.
    rewrite Word.Properties.word.eqb_eq in P by reflexivity.
    discriminate.
  Qed.

  Lemma isXAddr1B_true: forall a xAddrs,
      isXAddr1 a xAddrs -> isXAddr1B a xAddrs = true.
  Proof.
    intros. destruct (isXAddr1B a xAddrs) eqn: E; [reflexivity|exfalso].
    eapply isXAddr1B_not; eassumption.
  Qed.

  Lemma isXAddr1B_false: forall a xAddrs,
      ~ isXAddr1 a xAddrs -> isXAddr1B a xAddrs = false.
  Proof.
    intros. destruct (isXAddr1B a xAddrs) eqn: E; [exfalso|reflexivity].
    apply isXAddr1B_holds in E. contradiction.
  Qed.

  Lemma isXAddr4B_holds: forall a xAddrs,
      isXAddr4B a xAddrs = true -> isXAddr4 a xAddrs.
  Proof.
    unfold isXAddr4B, isXAddr4. intros.
    apply andb_prop in H. destruct H as [H ?].
    apply andb_prop in H. destruct H as [H ?].
    apply andb_prop in H. destruct H as [H ?].
    apply isXAddr1B_holds in H.
    apply isXAddr1B_holds in H0.
    apply isXAddr1B_holds in H1.
    apply isXAddr1B_holds in H2.
    auto.
  Qed.

  Lemma isXAddr4B_not: forall a xAddrs,
      isXAddr4B a xAddrs = false -> ~ isXAddr4 a xAddrs.
  Proof.
    unfold isXAddr4B, isXAddr4. intros.
    intros [C0 [C1 [C2 C3]]].
    apply isXAddr1B_true in C0. rewrite C0 in H.
    apply isXAddr1B_true in C1. rewrite C1 in H.
    apply isXAddr1B_true in C2. rewrite C2 in H.
    apply isXAddr1B_true in C3. rewrite C3 in H.
    discriminate H.
  Qed.

  Lemma isXAddr4B_true: forall a xAddrs,
      isXAddr4 a xAddrs -> isXAddr4B a xAddrs = true.
  Proof.
    intros. destruct (isXAddr4B a xAddrs) eqn: E; [reflexivity|exfalso].
    eapply isXAddr4B_not; eassumption.
  Qed.

  Lemma isXAddr4B_false: forall a xAddrs,
      ~ isXAddr4 a xAddrs -> isXAddr4B a xAddrs = false.
  Proof.
    intros. destruct (isXAddr4B a xAddrs) eqn: E; [exfalso|reflexivity].
    apply isXAddr4B_holds in E. contradiction.
  Qed.

  Definition removeXAddr(a: word): XAddrs -> XAddrs :=
    List.filter (fun a' => negb (word.eqb a a')).

  Definition addXAddr: word -> XAddrs -> XAddrs := List.cons.

  Fixpoint addXAddrRange(a: word)(nBytes: nat)(xAddrs: XAddrs): XAddrs :=
    match nBytes with
    | O => xAddrs
    | S n => addXAddr a (addXAddrRange (word.add a (word.of_Z 1)) n xAddrs)
    end.

  Section WithBitwidth.
    Context {BW: Bitwidth width}.

    Record RiscvMachine := mkRiscvMachine {
      getRegs: Registers;
      getPc: word;
      getNextPc: word;
      getMem: Mem;
      getXAddrs: XAddrs;
      getLog: list LogItem;
    }.

    Definition withRegs: Registers -> RiscvMachine -> RiscvMachine :=
      fun regs2 '(mkRiscvMachine regs1 pc nextPC mem xAddrs log) =>
                  mkRiscvMachine regs2 pc nextPC mem xAddrs log.

    Definition withPc: word -> RiscvMachine -> RiscvMachine :=
      fun pc2 '(mkRiscvMachine regs pc1 nextPC mem xAddrs log) =>
                mkRiscvMachine regs pc2 nextPC mem xAddrs log.

    Definition withNextPc: word -> RiscvMachine -> RiscvMachine :=
      fun nextPC2 '(mkRiscvMachine regs pc nextPC1 mem xAddrs log) =>
                    mkRiscvMachine regs pc nextPC2 mem xAddrs log.

    Definition withMem: Mem -> RiscvMachine -> RiscvMachine :=
      fun mem2 '(mkRiscvMachine regs pc nextPC mem1 xAddrs log)  =>
                 mkRiscvMachine regs pc nextPC mem2 xAddrs log.

    Definition withXAddrs: XAddrs -> RiscvMachine -> RiscvMachine :=
      fun xAddrs2 '(mkRiscvMachine regs pc nextPC mem xAddrs1 log)  =>
                    mkRiscvMachine regs pc nextPC mem xAddrs2 log.

    Definition withLog: list LogItem -> RiscvMachine -> RiscvMachine :=
      fun log2 '(mkRiscvMachine regs pc nextPC mem xAddrs log1) =>
                 mkRiscvMachine regs pc nextPC mem xAddrs log2.

    Definition withLogItem: LogItem -> RiscvMachine -> RiscvMachine :=
      fun item '(mkRiscvMachine regs pc nextPC mem xAddrs log) =>
                 mkRiscvMachine regs pc nextPC mem xAddrs (item :: log).

    Definition withLogItems: list LogItem -> RiscvMachine -> RiscvMachine :=
      fun items '(mkRiscvMachine regs pc nextPC mem xAddrs log) =>
                  mkRiscvMachine regs pc nextPC mem xAddrs (items ++ log).

    Definition Z32s_to_bytes(l: list Z): list byte :=
      List.flat_map (fun z => HList.tuple.to_list (LittleEndian.split 4 z)) l.

    Definition putProgram(prog: list MachineInt)(addr: word)(ma: RiscvMachine): RiscvMachine :=
      (withPc addr
      (withNextPc (word.add addr (word.of_Z 4))
      (withXAddrs (addXAddrRange addr (4 * List.length prog) ma.(getXAddrs))
      (withMem (unchecked_store_byte_list addr (Z32s_to_bytes prog) ma.(getMem)) ma)))).

  End WithBitwidth.
End Machine.
