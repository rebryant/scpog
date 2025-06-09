# d4 project

This is a modified version of the D4v2 code, downloaded from https://github.com/crillab/d4v2

Modifications include the following:
   * Support for SCPOG generation.
     	When the --skolemize flag is set to 1, it will include quantified literals in the DNNF output
   * A quiet flag.  Set --quiet to 1
   * Compatible with LLVM compiler for x86 and ARM-based Macs.
        This involved changing some names of included files and eliminating library code only provided with GCC.
   * Use standard makefiles, rather than the ninja build system

# d4 project

# How to Compile

```console
$ make all -f Makefile-compile MACHINE=XXXX
```

where XXXX can be 'linux', 'mac', or 'arm'.
The executable is called 'd4t'

# Other actions

```console
$ make clean -f Makefile-compile 
```

Remove all files added during compilation

