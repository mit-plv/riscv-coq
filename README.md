# RISC-V Specification in Coq

Generated from the [RISCV Semantics in Haskell](https://github.com/mit-plv/riscv-semantics) using [hs-to-coq](https://github.com/antalsz/hs-to-coq), with some manually written Coq files too.
Currently, the architectures RV32I and RV64I with any combination of the extensions A and M are supported.


### Build

You will need the latest released version of Coq, or master.

`riscv-coq` depends on the `coqutil` library. You can get this dependency and build the project using the following commands:

```
git clone https://github.com/mit-plv/coqutil.git
git clone https://github.com/mit-plv/riscv-coq.git
make -C coqutil
cd riscv-coq/
make
```


### If it doesn't build

If something doesn't work, you could try to do exactly the same as [bedrock2](https://github.com/mit-plv/bedrock2/commits/master) does, which uses riscv-coq as a dependency and has continuous integration, so if you pick a commit with a green tick there, you can be sure to have a working version.
