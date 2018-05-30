(* Some Ltac code and Gallina notations which can be used to translate a goal about integer
   arithmetic into smtlib syntax, so that it can be fed to an SMT solver such as Z3. *)

Require Import Coq.omega.Omega.

Open Scope Z_scope.

Definition marker(P: Prop): Prop := P.

Lemma test: forall
  (opcode rs1 rs2 funct3 simm12
  inst q q0 r1 r2
  r r0 q1 q2 q3 r3 q4 r4 q5 r5 q6 r6 q7 r7 q8 r8 q9 r9 q10 r10 q11 r11 q12
  r12 q13 r13 q14 r14 q15 r15 q16 r16: Z),
    0 <= opcode < 128 /\ 0 <= rs1 < 32 /\ 0 <= rs2 < 32 /\
    0 <= funct3 < 8 /\ - (2048) <= simm12 < 2048
  -> opcode + r1 * 128 + funct3 * 4096 + rs1 * 32768 + rs2 * 1048576 + r2 * 33554432 = inst
  -> 0 <= r16 < 2
  -> q9 = 2 * q16 + r16
  -> 0 <= r15 < 32
  -> q6 = 32 * q15 + r15
  -> 0 <= r14 < 32
  -> q5 = 32 * q14 + r14
  -> 0 <= r13 < 8
  -> q4 = 8 * q13 + r13
  -> 0 <= r12 < 128
  -> q3 = 128 * q12 + r12
  -> 0 <= r11 < 32
  -> q8 = 32 * q11 + r11
  -> 0 <= r10 < 128
  -> q7 = 128 * q10 + r10
  -> 0 <= r9 < 2048
  -> r10 * 32 + r11 = 2048 * q9 + r9
  -> 0 <= r8 < 128
  -> inst = 128 * q8 + r8
  -> 0 <= r7 < 33554432
  -> inst = 33554432 * q7 + r7
  -> 0 <= r6 < 1048576
  -> inst = 1048576 * q6 + r6
  -> 0 <= r5 < 32768
  -> inst = 32768 * q5 + r5
  -> 0 <= r4 < 4096
  -> inst = 4096 * q4 + r4
  -> 0 <= r3 < 1
  -> inst = 1 * q3 + r3
  -> 0 <= r2 < 128
  -> q0 = 128 * q2 + r2
  -> 0 <= r1 < 32
  -> q = 32 * q1 + r1
  -> 0 <= r0 < 32
  -> simm12 = 32 * q0 + r0
  -> 0 <= r < 1
  -> simm12 = 1 * q + r
  -> opcode = r12 /\ funct3 = r13 /\ rs1 = r14
     /\ rs2 = r15 /\ simm12 = r10 * 32 + r11 - r16 * 4096.
Proof.
  intros.
  
  repeat match goal with
         | H: ?T |- _ => match T with
                         | Z => fail 1
                         | _ => revert H
                         end
         end.
  match goal with
  | |- ?P => change (marker P)
  end.
  repeat match goal with
         | H: _ |- _ => revert H
         end.
  match goal with
  | |- ?P => assert (~P)
  end.
  {
    assert (forall A (P: A -> Prop), (exists a: A, ~ P a) <-> ~ forall (a: A), P a) as E. {
      intros. split.
      - intros. destruct H as [a H]. intro. apply H. auto.
      - intro. admit. (* classical logic *)
    }
    rewrite <- E.
    do 10 setoid_rewrite <- E.
    do 10 setoid_rewrite <- E.
    do 10 setoid_rewrite <- E.
    do 10 setoid_rewrite <- E.
    do 1 setoid_rewrite <- E.

    assert (forall (P Q: Prop), (~ (P -> Q)) <-> (P /\ ~ Q)) as F by admit.
    assert (forall (P Q: Prop), (~ marker (P -> Q)) <-> marker (P /\ ~ Q)) as F'. {
      cbv [marker]. exact F.
    }
    do 10 setoid_rewrite F.
    do 10 setoid_rewrite F.
    do 10 setoid_rewrite F.
    do 5 setoid_rewrite F.
    do 3 setoid_rewrite F.
    
    Set Printing Depth 100.

    assert (forall (P Q: Prop), ~ (P /\ Q) <-> (~ P) \/ (~ Q)) as G by admit.
    do 4 setoid_rewrite G.

    assert (forall (P Q: Z -> Prop), ex (fun (z: Z) => P z /\ Q z)
                                     <-> ex (fun (z: Z) => marker (P z /\ Q z))) as K. {
      intros. cbv [marker]. reflexivity.
    }
    setoid_rewrite K.
    
    Notation "'and' A B" := (Logic.and A B) (at level 10, A at level 0, B at level 0).
    Notation "'or' A B" := (Logic.or A B) (at level 10, A at level 0, B at level 0).
    Notation "+ A B" := (Z.add A B) (at level 10, A at level 0, B at level 0).
    Notation "< A B" := (Z.lt A B) (at level 10, A at level 0, B at level 0).
    Notation "<= A B" := (Z.le A B) (at level 10, A at level 0, B at level 0).
    Notation "- A B" := (Z.sub A B) (at level 10, A at level 0, B at level 0).
    Notation "* A B" := (Z.mul A B) (at level 10, A at level 0, B at level 0,
                                    format " *  A  B").
    Notation "= A B" := (@eq Z A B) (at level 10, A at level 0, B at level 0).
    Notation "'not' A" := (not A) (at level 10, A at level 0).

    Notation "'(declare-const' a 'Int)' body" := (ex (fun (a: Z) => body))
               (at level 10, body at level 10,
                format "(declare-const  a  Int) '//' body").
    Notation "'(assert' P ')'" := (marker P)
               (at level 10, P at level 0,
                format "(assert  P )").
    Notation "- 0 a" := (Z.opp a) (at level 10, a at level 10).

    idtac.
    (* If we append "(check-sat)" to this goal and feed it into z3, we get "unsat",
       so there's no counterexample, so the statement should be true and we know that
       we're on the right track. *)
Abort.

