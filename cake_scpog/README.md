# cake_scpog
This folder contains pre-compiled binaries of cake_scpog for verified projected model counting.

Source and proof files are available in the main CakeML repository (https://github.com/CakeML/cakeml/tree/master/examples/scpog_checker)

The files are built from the following repository versions

```
HOL4: 37389f39aa1f331637b2525ad92fdba43703a13e

CakeML: e1650fc504837c0fbd3931cc5066914ffdc9d877
```
# Instructions

Running `make` will build the proof checker `cake_scpog` by default using `gcc` for x64 machines.

To build for Mac (or other machines with ARMv8 chips) with `gcc`, run `make cake_scpog_arm8`.

You may need to tweak the Makefile for other variations (e.g., `clang`).

This help string is printed to stdout when cake_lpr is run with no arguments:

```
Usage:  cake_scpog <DIMACS formula file> <SCPOG file>

Run SCPOG proof checking
```

The default heap size is 8GB and default stack size is 4GB.

There are three ways to modify the default values:

1) Directly modify the values of `cml_heap_sz` and `cml_stack_sz` in `basis_ffi.c`.

2) Pass the appropriate flags, e.g., `-DCML_HEAP_SIZE=65536` `-DCML_STACK_SIZE=16384` at compile time.

3) Set the environment variables at run time:

  ```
  export CML_HEAP_SIZE=1234
  export CML_STACK_SIZE=5678
  ./cake_scpog foo.cnf bar.proof
  ```

We recommend giving more heap for proof checking if your system memory allows for it.
