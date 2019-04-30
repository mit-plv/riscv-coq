Require Import Coq.Strings.String.

Definition MMIOAction: Type := string.
Definition MMInput: MMIOAction := "MMInput"%string.
Definition MMOutput: MMIOAction := "MMOutput"%string.

Definition isMMInput: MMIOAction -> bool := String.eqb MMInput.
Definition isMMOutput: MMIOAction -> bool := String.eqb MMOutput.
