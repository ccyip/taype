# Taypsi

[![GitHub CI](https://github.com/ccyip/taype/workflows/CI/badge.svg)](https://github.com/ccyip/taype/actions)
[![Hackage](https://img.shields.io/hackage/v/taype.svg?logo=haskell)](https://hackage.haskell.org/package/taype)
[![MIT license](https://img.shields.io/badge/license-MIT-blue.svg)](LICENSE)

A policy-agnostic language for oblivious computation with algebraic data types.

Taypsi is an extension of the language Taype, with Ψ-type and static enforcement
of policies. We keep the compiler and source code name Taype, as Taypsi is
considered a new version of Taype.

## Build instructions

To build the `taype` type checker and compiler, we need the Haskell toolchain,
which can be easily installed with [ghcup](https://www.haskell.org/ghcup/).
Cabal will take care of the Haskell dependencies for us. We currently only test
on Haskell 9.4.7 and Cabal 3.10.2.

To build and run the examples, we need the OCaml toolchain which can be
installed with [opam](https://opam.ocaml.org/), and Taype drivers (implementing
the oblivious primitives). Note that this is not necessary if you only want to
type check Taype programs but not run them. The best-tested version is OCaml
4.14.1, although other versions probably also work.

You can create a new opam switch for Taype and install dependencies via:

``` sh
opam switch create taype --package=ocaml-variants.4.14.1+options,ocaml-option-flambda
opam update
opam install dune ctypes containers sexplib yojson
```

Then go to the repository of Taype drivers and follow the instructions there to
install the drivers.
- [Taype drivers repository](https://github.com/ccyip/taype-drivers.git)

Once these dependencies are installed, we can build the project by:

``` sh
cd solver
dune build
cd ..
cabal build
```

and build the examples by:

``` sh
cabal run shake
```

## Run the Taype compiler

We can execute the Taype compiler by:

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

We can also build an individual example, test an individual example against a
particular driver and so on. See the help message for more options and targets:

``` sh
cabal run shake -- --help
```

Notably, the `--round=N` option specifies how many rounds a test will be run,
and the `--verbose` option prints out the commands that are being executed.

If your EMP toolkit and `emp-ffi` libraries from Taype drivers were not
installed to a system prefix, running the examples with Emp toolkit backend
would not work. Assuming we install the driver to the opam prefix
`$OPAM_SWITCH_PREFIX` (so that it doesn't pollute our system), we can update the
environment variables for the library paths before running the examples:

``` sh
# on linux
export LD_LIBRARY_PATH "$OPAM_SWITCH_PREFIX/lib"

# on Mac
export DYLD_LIBRARY_PATH "$OPAM_SWITCH_PREFIX/lib"
```
