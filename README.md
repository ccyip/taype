# Taype

[![GitHub CI](https://github.com/ccyip/taype/workflows/CI/badge.svg)](https://github.com/ccyip/taype/actions)
[![Hackage](https://img.shields.io/hackage/v/taype.svg?logo=haskell)](https://hackage.haskell.org/package/taype)
[![MIT license](https://img.shields.io/badge/license-MIT-blue.svg)](LICENSE)

A policy-agnostic language for oblivious computation with algebraic data types.

## Build instructions

To build the `taype` type checker and compiler, we need the Haskell toolchain,
which can be easily installed with [ghcup](https://www.haskell.org/ghcup/).
Cabal will take care of the Haskell dependencies for us. We currently only tests
on Haskell 9.2.5 and Cabal 3.8.1.

To build and run the examples, we need the OCaml toolchain which can be
installed with [opam](https://opam.ocaml.org/), and taype drivers (implementing
the oblivious primitives). Note that this is not necessary if you only want to
type check taype programs but not run them. The best-tested version is OCaml
4.14.1, although other versions probably also work.

You can create a new opam switch for taype and install dependencies via:

``` sh
opam switch create taype --package=ocaml-variants.4.14.1+options,ocaml-option-flambda
opam update
opam install dune ctypes sexplib
```

Then go to the repositories of the taype drivers and follow the instructions
there to install the drivers. The plaintext driver (taype-driver-plaintext) and
the emp driver (taype-driver-emp) are required for the examples. They can be
found in the github repositories:
- [plaintext driver](https://github.com/ccyip/taype-driver-plaintext)
- [emp driver](https://github.com/ccyip/taype-driver-emp).

Once these dependencies are installed, we can build the project by:

``` sh
cabal build
```

and build the examples by:

``` sh
cabal run shake
```

## Run taype compiler

We can execute the taype compiler by:

``` sh
cabal run taype -- <arguments to taype>
```

For example, to type check and compile the tutorial program:

``` sh
cabal run taype -- examples/tutorial/tutorial.tp
```

Run the following command to see what options are available to the compiler.

``` sh
cabal run taype -- --help
```

## Build and run examples

Taype compiler only generates the OCaml target code from the taype source code.
We still need to compile the generated OCaml code and link with a driver. Doing
all these manually is quite tedious, so we use the [shake build
system](https://shakebuild.com/) to streamline the compilation and evaluation.

To build all examples, run:

``` sh
cabal run shake
```

To evaluate all examples, run:

``` sh
cabal run shake -- run
```

We can also build an individual example, test an individual example against one
driver and so on. See the help message for more options and targets:

``` sh
cabal run shake -- --help
```

Notably, the `--round=N` option specifies how many rounds a test will be run,
and the `--verbose` option prints out the commands that are being executed.

If your `taype-emp-driver` (specifically the `emp-ffi` dynamically linked
library) was not installed to a system prefix, running the examples with
emp-toolkit backend would not work. Assuming we install the driver to the opam
prefix `$OPAM_SWITCH_PREFIX` (so that it doesn't pollute our system), we can
update the environment variables for the library paths before running the
examples:

``` sh
# on linux
export LD_LIBRARY_PATH "$OPAM_SWITCH_PREFIX/lib"

# on Mac
export DYLD_LIBRARY_PATH "$OPAM_SWITCH_PREFIX/lib"
```
