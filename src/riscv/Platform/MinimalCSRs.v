Require Import Coq.ZArith.ZArith. Local Open Scope Z_scope.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List. Import ListNotations.
Require Import coqutil.Tactics.Tactics.
Require Import riscv.Spec.Machine.
Require Import riscv.Platform.Memory.
Require Import riscv.Spec.CSRFile.
Require Import riscv.Utility.Utility.
Require Import riscv.Utility.RecordSetters.
Require Import coqutil.Z.Lia.
Require Import coqutil.Map.Interface.
Require Import riscv.Platform.MaterializeRiscvProgram.

Module map.
  (* Swap argument order to enable usage of partially applied `map.set k v` as an updater *)
  Definition set{key value}{map: map.map key value}(k: key)(v: value)(m: map): map :=
    map.put m k v.
End map.

Section Riscv.
  Context {width: Z} {BW: Bitwidth width} {word: word width} {word_ok: word.ok word}.
  Context {Mem: map.map word byte}.
  Context {Registers: map.map Z word}.

  (* (memory before call, call name, arg values) and (memory after call, return values) *)
  Definition LogItem: Type := (Mem * string * list word) * (Mem * list word).

  Record State := mkState {
    regs: Registers;
    pc: word;
    nextPc: word;
    mem: Mem;
    log: list LogItem;
    csrs: CSRFile
  }.

  (* TODO: add XAddrs tracking so that executing an instruction written in a previous cycle
     (which potentially is already in the pipeline) is not allowed *)

  Definition store(n: nat)(ctxid: SourceType)(a: word) v (mach: State)(post: State -> Prop) :=
    match Memory.store_bytes n mach.(mem) a v with
    | Some m => post { mach with mem := m }
    | None => False
    end.

  Definition load(n: nat)(ctxid: SourceType)(a: word)(mach: State)(post: _ -> _ -> Prop) :=
    match Memory.load_bytes n mach.(mem) a with
    | Some v => post v mach
    | None => False
    end.

  Definition updatePc(mach: State): State :=
    { mach with pc := mach.(nextPc); nextPc ::= word.add (word.of_Z 4) }.

  Definition getReg(regs: Registers)(reg: Z): word :=
    if ((0 <? reg) && (reg <? 32))%bool then
      match map.get regs reg with
      | Some x => x
      | None => word.of_Z 0
      end
    else word.of_Z 0.

  Definition setReg(reg: Z)(v: word)(regs: Registers): Registers :=
    if ((0 <? reg) && (reg <? 32))%bool then map.put regs reg v else regs.

  Definition run_primitive(a: riscv_primitive)(mach: State):
             (primitive_result a -> State -> Prop) -> (State -> Prop) -> Prop :=
    match a with
    | GetRegister reg => fun postF postA => postF (getReg mach.(regs) reg) mach
    | SetRegister reg v => fun postF postA => postF tt { mach with regs ::= setReg reg v }
    | GetPC => fun postF postA => postF mach.(pc) mach
    | SetPC newPC => fun postF postA => postF tt { mach with nextPc := newPC }
    | LoadByte ctxid a => fun postF postA => load 1 ctxid a mach postF
    | LoadHalf ctxid a => fun postF postA => load 2 ctxid a mach postF
    | LoadWord ctxid a => fun postF postA => load 4 ctxid a mach postF
    | LoadDouble ctxid a => fun postF postA => load 8 ctxid a mach postF
    | StoreByte ctxid a v => fun postF postA => store 1 ctxid a v mach (postF tt)
    | StoreHalf ctxid a v => fun postF postA => store 2 ctxid a v mach (postF tt)
    | StoreWord ctxid a v => fun postF postA => store 4 ctxid a v mach (postF tt)
    | StoreDouble ctxid a v => fun postF postA => store 8 ctxid a v mach (postF tt)
    | StartCycle => fun postF postA =>
        postF tt { mach with nextPc := word.add mach.(pc) (word.of_Z 4) }
    | EndCycleNormal => fun postF postA => postF tt (updatePc mach)
    | EndCycleEarly _ => fun postF postA => postA (updatePc mach) (* ignores postF containing the continuation *)
    | GetCSRField f => fun postF postA =>
                         match map.get mach.(csrs) f with
                         | Some v => postF v mach
                         | None => False
                         end
    | SetCSRField f v => fun postF postA =>
                           (* only allow setting CSR fields that are supported (not None) on this machine *)
                           match map.get mach.(csrs) f with
                           | Some _ => postF tt { mach with csrs ::= map.set f v }
                           | None => False
                           end
    | GetPrivMode => fun postF postA => postF Machine mach
    | SetPrivMode mode => fun postF postA =>
                            match mode with
                            | Machine => postF tt mach
                            | User | Supervisor => False
                            end
    | MakeReservation _
    | ClearReservation _
    | CheckReservation _
    | Fence _ _
        => fun postF postA => False
    end.

  Lemma weaken_load: forall n c a m (post1 post2:_->_->Prop),
      (forall r s, post1 r s -> post2 r s) ->
      load n c a m post1 -> load n c a m post2.
  Proof.
    unfold load. intros. destruct (load_bytes n m.(mem) a); intuition eauto.
  Qed.

  Lemma weaken_store: forall n c a v m (post1 post2:_->Prop),
      (forall s, post1 s -> post2 s) ->
      store n c a v m post1 -> store n c a v m post2.
  Proof.
    unfold store. intros. destruct (store_bytes n m.(mem) a v); intuition eauto.
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
