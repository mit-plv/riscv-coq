Require Import Coq.Strings.String.
Require Import Coq.ZArith.BinInt.
Require Import coqutil.Map.Interface.
Require Import coqutil.Word.Interface.
Require Import coqutil.Word.LittleEndian.
Require Import riscv.Spec.Decode.
Require Import riscv.Platform.Memory.
Require Import riscv.Utility.Utility.


Section Machine.

  Context {W: Words}.
  Context {Registers: map.map Register word}.
  Context {Mem: map.map word byte}.

  (* (memory before call, call name, arg values) and (memory after call, return values) *)
  Definition LogItem: Type := (Mem * string * list word) * (Mem * list word).

  (* set of executable addresses. On some processors, this could be the whole address range,
     while on others, only a specific range. And when an address is written, we might
     conservatively remove it from that set if we want to prove that our software does not
     depend on self-modifying code being possible.
     The ifence instruction can will flush the instruction cache and therefore put back the
     set of executable addresses to the whole range.
     We only store 4-byte aligned addresses, and storeByte has to clear the two low bits. *)
  Definition XAddrs: Type := list word.

  Definition isXAddrB(a: word)(xAddrs: XAddrs): bool :=
    match List.find (word.eqb a) xAddrs with
    | Some _ => true
    | None => false
    end.

  Definition isXAddr: word -> XAddrs -> Prop := @List.In word.

  Lemma isXAddrB_holds: forall a xAddrs,
      isXAddrB a xAddrs = true -> isXAddr a xAddrs.
  Proof.
    unfold isXAddrB, isXAddr. intros.
    destruct (List.find (word.eqb a) xAddrs) eqn: E; [|discriminate].
    apply List.find_some in E. destruct E.
    apply Word.Properties.word.eqb_true in H1.
    subst. assumption.
  Qed.

  Lemma isXAddrB_not: forall a xAddrs,
      isXAddrB a xAddrs = false -> ~ isXAddr a xAddrs.
  Proof.
    unfold isXAddrB, isXAddr. intros.
    destruct (List.find (word.eqb a) xAddrs) eqn: E; [discriminate|].
    intro C.
    pose proof (List.find_none _ _ E _ C) as P.
    rewrite Word.Properties.word.eqb_eq in P by reflexivity.
    discriminate.
  Qed.

  Lemma isXAddrB_true: forall a xAddrs,
      isXAddr a xAddrs -> isXAddrB a xAddrs = true.
  Proof.
    intros. destruct (isXAddrB a xAddrs) eqn: E; [reflexivity|exfalso].
    eapply isXAddrB_not; eassumption.
  Qed.

  Lemma isXAddrB_false: forall a xAddrs,
      ~ isXAddr a xAddrs -> isXAddrB a xAddrs = false.
  Proof.
    intros. destruct (isXAddrB a xAddrs) eqn: E; [exfalso|reflexivity].
    apply isXAddrB_holds in E. contradiction.
  Qed.

  Definition removeXAddr(a: word): XAddrs -> XAddrs :=
    List.filter (fun a' => negb (word.eqb a a')).

  Definition addXAddr: word -> XAddrs -> XAddrs := List.cons.

  Fixpoint addXAddrRange(a: word)(nWords: nat)(xAddrs: XAddrs): XAddrs :=
    match nWords with
    | O => xAddrs
    | S n => addXAddr a (addXAddrRange (word.add a (word.of_Z 4)) n xAddrs)
    end.

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
    (withXAddrs (addXAddrRange addr (List.length prog) ma.(getXAddrs))
    (withMem (unchecked_store_byte_list addr (Z32s_to_bytes prog) ma.(getMem)) ma)))).

End Machine.
