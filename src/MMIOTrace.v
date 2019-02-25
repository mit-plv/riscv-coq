(*
We do not do this:

Inductive MMIOAction := MMInput | MMOutput.

Because other libraries (such as bedrock2/bedrock2) don't depend on riscv-coq, but should
still be able to use the same data type in their trace.
*)

Definition MMIOAction: Type := bool.
Definition MMInput: MMIOAction := false.
Definition MMOutput: MMIOAction := true.

Definition isMMInput(a: MMIOAction): bool := negb a.
Definition isMMOutput(a: MMIOAction): bool := a.
