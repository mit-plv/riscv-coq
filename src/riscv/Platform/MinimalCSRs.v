Require Import Coq.ZArith.ZArith. Local Open Scope Z_scope.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List. Import ListNotations.
Require Import coqutil.Tactics.Tactics.
Require Import riscv.Spec.Machine.
Require Import riscv.Platform.Memory.
Require Import riscv.Spec.CSRFile.
Require Import riscv.Utility.Utility.
Require Import riscv.Utility.StringRecords.
Import RecordNotations. (* Warnings are spurious, COQBUG https://github.com/coq/coq/issues/13058 *)
Require Import coqutil.Z.Lia.
Require Import coqutil.Map.Interface.
Require Import riscv.Platform.MaterializeRiscvProgram.

Section Riscv.
  Context {W: Words}.
  Context {Mem: map.map word byte}.
  Context {Registers: map.map Z word}.

  (* (memory before call, call name, arg values) and (memory after call, return values) *)
  Definition LogItem: Type := (Mem * string * list word) * (Mem * list word).

  Definition State: Type := [#
    "regs": Registers;
    "pc": word;
    "nextPc": word;
    "mem": Mem;
    "log": list LogItem;
    "csrs": CSRFile
   ].

  (* TODO: add XAddrs tracking so that executing an instruction written in a previous cycle
     (which potentially is already in the pipeline) is not allowed *)

  Definition store(n: nat)(ctxid: SourceType)(a: word) v (mach: State)(post: State -> Prop) :=
    match Memory.store_bytes n mach#"mem" a v with
    | Some m => post mach(#"mem" := m)
    | None => False
    end.

  Definition load(n: nat)(ctxid: SourceType)(a: word)(mach: State)(post: _ -> _ -> Prop) :=
    match Memory.load_bytes n mach#"mem" a with
    | Some v => post v mach
    | None => False
    end.

  Definition updatePc(mach: State): State :=
    mach(#"pc" := mach#"nextPc")(#"nextPc" := word.add mach#"nextPc" (word.of_Z 4)).

  Definition run_primitive(a: riscv_primitive)(mach: State):
             (primitive_result a -> State -> Prop) -> (State -> Prop) -> Prop :=
    match a with
    | getRegister reg => fun postF postA =>
        let v :=
          if Z.eq_dec reg 0 then word.of_Z 0
          else match map.get mach#"regs" reg with
               | Some x => x
               | None => word.of_Z 0 end in
        postF v mach
    | setRegister reg v => fun postF postA =>
      let regs := if Z.eq_dec reg Register0
                  then mach#"regs"
                  else map.put mach#"regs" reg v in
      postF tt mach(#"regs" := regs)
    | getPC => fun postF postA => postF mach#"pc" mach
    | setPC newPC => fun postF postA => postF tt mach(#"nextPc" := newPC)
    | loadByte ctxid a => fun postF postA => load 1 ctxid a mach postF
    | loadHalf ctxid a => fun postF postA => load 2 ctxid a mach postF
    | loadWord ctxid a => fun postF postA => load 4 ctxid a mach postF
    | loadDouble ctxid a => fun postF postA => load 8 ctxid a mach postF
    | storeByte ctxid a v => fun postF postA => store 1 ctxid a v mach (postF tt)
    | storeHalf ctxid a v => fun postF postA => store 2 ctxid a v mach (postF tt)
    | storeWord ctxid a v => fun postF postA => store 4 ctxid a v mach (postF tt)
    | storeDouble ctxid a v => fun postF postA => store 8 ctxid a v mach (postF tt)
    | endCycleNormal => fun postF postA => postF tt (updatePc mach)
    | endCycleEarly _ => fun postF postA => postA (updatePc mach) (* ignores postF containing the continuation *)
    | getCSRField f => fun postF postA =>
                         match map.get mach#"csrs" f with
                         | Some v => postF v mach
                         | None => False
                         end
    | setCSRField f v => fun postF postA =>
                           (* only allow setting CSR fields that are supported (not None) on this machine *)
                           match map.get mach#"csrs" f with
                           | Some _ => postF tt mach(#"csrs" := map.put mach#"csrs" f v)
                           | None => False
                           end
    | getPrivMode => fun postF postA => postF Machine mach
    | setPrivMode mode => fun postF postA =>
                            match mode with
                            | Machine => postF tt mach
                            | User | Supervisor => False
                            end
    | makeReservation _
    | clearReservation _
    | checkReservation _
        => fun postF postA => False
    end.

  Lemma weaken_load: forall n c a m (post1 post2:_->_->Prop),
      (forall r s, post1 r s -> post2 r s) ->
      load n c a m post1 -> load n c a m post2.
  Proof.
    unfold load. intros. destruct (load_bytes n m#"mem" a); intuition eauto.
  Qed.

  Lemma weaken_store: forall n c a v m (post1 post2:_->Prop),
      (forall s, post1 s -> post2 s) ->
      store n c a v m post1 -> store n c a v m post2.
  Proof.
    unfold store. intros. destruct (store_bytes n m#"mem" a v); intuition eauto.
  Qed.

  Lemma weaken_run_primitive: forall a (postF1 postF2: _ -> _ -> Prop) (postA1 postA2: _ -> Prop),
    (forall r s, postF1 r s -> postF2 r s) ->
    (forall s, postA1 s -> postA2 s) ->
    forall s, run_primitive a s postF1 postA1 -> run_primitive a s postF2 postA2.
  Proof.
    destruct a; cbn; intros; try solve [intuition eauto using weaken_load, weaken_store];
      destruct_one_match; eauto.
  Qed.

End Riscv.
