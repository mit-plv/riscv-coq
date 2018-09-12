Require Extraction.

Require Import riscv.Example.

Extraction Language JSON.
Set Warnings "-extraction-reserved-identifier".

Extraction NoInline Coq.Init.Datatypes.orb.
Extraction NoInline Coq.Init.Datatypes.andb.

Recursive Extraction Library Example.
