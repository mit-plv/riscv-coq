How the code is structured.

This specification defines all instructions of the RISCV-ISA in terms of a few
primitive “methods” whose signature is declared in the typclass `RiscvMachine`
in `src/Spec/Machine.v`. These “methods” include, for example, getting and
setting registers and memory.
Note that the `RiscvMachine` typeclass abstracts over the data type used to
represent the state of the computer. This makes the specification very
flexible, and allows us to use the same definitions of `execute` with different
state reperesentations: Someone might want to use a simple record such as
`Platform.RiscvMachine.RiscvMachine`, while others might want to use a “set of
possible states of the machine” to model non-determinism
(`Platform.MinimalMMIO` does that, for instance, by using the non-determinism
monad `OStateND`), or a history of all invocations of primitive “methods” could
also serve as a state representation, which might be more suitable to reason
about interleaved execution on several cores.

The `run` function defined in `src/Platform/Run.v` takes an instance of the
`RiscvMachine` typeclass and uses the `decode` and `execute` functions defined
in `src/Spec` to execute a specified number of instructions. The instruction
set (RV32 or RV64 and which extensions) have to be given as parameter.
The function `execute` defined in `src/Spec/Execute.v` uses the “methods” of
the `RiscvMachine` to define how each instruction acts on the machine.

The following mental image might help: an implementor of a
`RiscvMachine`-Instance provides the management of the state, while `run`,
`decode` and `execute` contain the controlling circuitry, managing operations
and calculations.

--

It is always important to tell the difference between
`Spec.Machine.RiscvMachine` and `Platform.RiscvMachine.RiscvMachine`. The
former being the typeclass discussed above, while the latter is a Record used
in most (currently all) instances of that typeclass.

--

The files `src/Spec/Primitives.v` and `src/Spec/MetricPrimitives.v` define when
an instance of the `RiscvMachine` typeclass is “well-behaved”.
When instances of `RiscvMachine` can be used to instantiate `Primitives`, they
are well-behaved (relative to the parameters used to construct the instance of
`Primitives`).

`MetricPrimitives` is concerned with the counting of usages of the methods of
`RiscvMachine`.

The `Primitives` typeclass is defined in a very abstract and general way.

Note that it is inherently impossible for `mcomp_sat` and the other members of
`PrimitivesParams` to be defined more specifically using the type system. They
are instantiated with functions that may know the implementation of the
Machine. A proof of well-behaviour using `Primitives` is always relative to the
given `PrimitivesParams`.
