# Getting Started Guide

This is the artifact for the PLDI 2023 paper ["Taype: a Policy-Agnostic Language
for Oblivious Computation"](https://doi.org/10.1145/3591261). This artifact is a
docker image, which contains:
- This README file, located at `~/README.md`.
- The docker file used to generate the docker image, located at `~/Dockerfile`.
- The implementation of the Taype type checker and compiler, written
  in Haskell, located at `~/taype`.
- Two drivers implementing the cryptographic primitives, as described in Section
  5 of the paper: a plaintext driver and a cryptographic driver based on [EMP
  toolkit](https://github.com/emp-toolkit/emp-tool). The plaintext and
  cryptographic drivers are located at `~/taype-driver-plaintext` and
  `~/taype-driver-emp`, respectively.
- All examples and experiments from the paper can be found in
  `~/taype/examples`. Since Taype programs are compiled to OCaml libraries, our
  test cases are also written in OCaml, which handle IO and invoke these
  libraries.
- Coq formalization of the Taype core calculus, based on [Ye and Delaware,
  Oblivious Algebraic Data Types, POPL22](https://doi.org/10.1145/3498713),
  located at `~/taype-theories`.
- A [code-server](https://github.com/coder/code-server) (VS Code in the
  browser), so that we can view source code and interpret experiment results
  simply in a browser (this is not required, of course). We pre-installed a few
  VS Code extensions:
  + Taype: for reading Taype source code. This extension provides basic syntax
    highlighting for Taype, Core Taype and OIL
  + Haskell: for reading source code of the Taype compiler
  + OCaml: for reading source code of the test cases and the generated OCaml
    code
  + VsCoq: for reading Coq formalization
  + Python (with Jupyter notebook): for interpreting and plotting our experimental
    results

All the implementations in the docker image have been pre-compiled. The clean
version of the source code, this README file and the docker file are also
available on [Zenodo](https://doi.org/10.5281/zenodo.7806981).

To evaluate this artifact, first install [docker](https://www.docker.com/), and
then download one of our docker images from Zenodo, depending on your machine's
architecture. We provide images for amd64 (i.e. x86-64) and arm64 (e.g., for
Apple Silicon Mac). You need around 12 GB of storage space to load them, and at
least 4 GB of RAM for the container to run the experiments.

Now you can load and run the downloaded docker image. The following commands
create an image called `taype-image`, and start a container called `taype`. We
also expose the port `8080` which can be used to access the code-server.

``` sh
# <arch> is amd64 or arm64
mv taype-image-<arch>.tar.xz taype-image.tar.xz
# This command will take a minute or two
docker load -i taype-image.tar.xz
docker run -dt -p 8080:8080 --name taype taype-image
```

Make sure the container can use at least 4 GB of memory. You can check the
memory limit by running `docker stats`.

To launch the code-server, run:

``` sh
docker exec -d taype code-server
```

Now we can open the URL [localhost:8080](http://localhost:8080) (or
[127.0.0.1:8080](http://127.0.0.1:8080)) in a browser to access VS Code. Note
that some functionality may not work if you use private mode or incognito mode.
You may read this markdown file (`~/README.md`) with a nicely rendered preview.
We did not pre-install the Haskell language server or the OCaml language server
in the docker image, but you can install them (more instructions are available
in the [next section](#step-by-step-instructions)). You may install other
extensions too.

To access the shell in the container, run:

``` sh
# --login is needed to setup the environment for Haskell and OCaml toolchains
docker exec -it taype bash --login
```

Your user name is `reviewer` (without password) and the current directory is `~`
(i.e. `/home/reviewer`). In the rest of this document, we assume commands are
run inside the container.

To quickly test this artifact, compile the tutorial example and run its test
cases.

``` sh
cd taype
cabal run shake -- run/tutorial
```

We will explain what exactly this command is doing in the next section, but you
should see the output of the tests. These contain headers like

`== Test case 1 (round 1) ==`

and then a few numbers for the performance statistics. This command also
generates CSV files (in this case
`examples/output/tutorial/test_elem.plaintext.output.csv` and
`examples/output/tutorial/test_elem.emp.output.csv`) which can be used by our
Python script for plotting.


# Step-by-Step Instructions

This section provides details on how the figures (claims) in the paper
correspond to the implementation, how to reproduce the experimental results, how
to use our tools, and the minor discrepancies between the implementation and the
paper's description.

## How to read code

As mentioned in the previous section, you can read the source code in the
browser with code-server. The docker image also comes with vim, if you prefer
reading source code in the console, but we do not have a syntax highlighting
extension for vim (yet).

You may want to install Haskell and OCaml language server for richer IDE
features such as jump to definition. You can install them by running:

``` sh
# Install Haskell language server
# This step may not be needed, as the Haskell VS Code extension may ask and do this for you
ghcup install hls

# Install OCaml language server
opam install ocaml-lsp-server
```

## Correspondence between paper and artifact

To see how this artifact connects to our approach described in the paper, we
summarize the correspondence in the following table. For presentation purposes,
the Taype syntax in the paper uses hat, subscripts, math symbols and so on,
which can not be typed in the source code, so the concrete syntax is different,
which we will summerize later.

| In paper | In artifact | Comment |
| -------- | ----------- | ------- |
| Fig. 1 | See [Understand the compilation pipeline](#understand-the-compilation-pipeline) | |
| Fig. 2 | `list` and `elem` in `taype/examples/tutorial/tutorial.tp` | This tutorial also includes an insertion function that is not presented in the paper |
| Fig. 3 | `` `list `` in `taype/examples/tutorial/tutorial.tp`, and `patient`, `patient_view` and `` `patient `` in `taype/examples/record/record.tp` | |
| Fig. 5 | `s_list`, `r_list` and `` `elem `` in `taype/examples/tutorial/tutorial.tp` | |
| Fig. 6 | `elem_C` to the left is `elem` in `taype/examples/tutorial/tutorial.tpc`, and `elem_O` to the right is `elem` in `taype/examples/tutorial/tutorial.oil` | See note 1 |
| Fig. 7 | `~@`, `~int`, `~s_int` and `~tape` in `taype/examples/common/prelude.oil` and `` `list `` in `taype/examples/tutorial/tutorial.oil` | The naming discrepancy will be discussed shortly |
| Fig. 8 | `Expr`, `Def` and `Label` in `taype/src/Taype/Syntax.hs` | The `Expr` and `Def` data types are supersets of both surface Taype and core Taype syntax, using *locally nameless representation* for binders |
| Fig. 9 and Fig. 10 | See [Coq formalization of the core calculus](#coq-formalization-of-the-core-calculus) | |
| Section 3.5 | `taype/src/Taype/TypeChecker.hs` | This is the implementation of our bidirectional type checker |
| Fig. 11 | `Expr`, `Ty` and `Def` in `taype/src/Oil/Syntax.hs` | Some operations do not have specific constructors in these data types: they are simply global names |
| Fig. 12 | `toOilTy` in `taype/src/Oil/Translation.hs` | |
| Fig. 13 | `toOilExpr` in `taype/src/Oil/Translation.hs` | |
| Fig. 14 | `list`, `~list`, and `~case#list` in `taype/examples/tutorial/tutorial.oil` | See note 1 |
| Fig. 15 | `toOilADTDef` in `taype/src/Oil/Translation.hs` | |
| Fig. 16 | `toOilSize` in `taype/src/Oil/Translation.hs` | |
| Fig. 17 | `` `inl `` in `taype/examples/common/prelude.oil` | |
| Fig. 18 | `toOilDef` in `taype/src/Oil/Translation.hs` | |
| Section 4.3 | `toOilProgram` in `taype/src/Oil/Translation.hs` | |
| Section 6.1 and Fig. 19 | `taype/examples/record/record.tp` | The corresponding functions have the same or similar names as in the figure |
| Section 6.2 and Fig. 19 (`secure-calculator`) | `taype/examples/calculator/calculator.tp` and `taype/examples/calculator/test_calculator.ml` | |
| Fig. 19 (`voting`) | `taype/examples/misc/misc.tp` | |
| Fig. 19 (`k-means`) | `taype/examples/kmeans/kmeans.tp` | |
| Section 6.3 | `taype/examples/dtree/dtree.tp`, `taype/examples/tree/tree.tp` and `taype/examples/list/list.tp` | This is the Taype source code of the examples for the microbenchmarks |
| Fig. 21 (a) | `dtree` and `` `dtree_all `` in `taype/examples/dtree/dtree.tp` | |
| Fig. 21 (b) | `` `dtree_max `` in `taype/examples/dtree/dtree.tp` | |
| Fig. 21 (c) | `spine` and `` `dtree_spine `` in `taype/examples/dtree/dtree.tp` | |
| Fig. 21 (d) | `spineF` and `` `dtree_spineF `` in `taype/examples/dtree/dtree.tp` | |
| Fig. 22 and 23 | See [Reproduce the experiment results](#reproduce-the-experiment-results) | |

Our main claim is that the security concern and the program logic can be cleanly
separated in the Taype language. We can verify this claim by checking the Taype
examples in `taype/examples`, such as `taype/examples/tutorial/tutorial.tp`: the
functionalities (e.g., `list` type, `elem` and `insert` functions) are coded as
conventional functional programs, independent of the security policies.

Notes:
1. The files with extensions `.tpc` and `.oil` are generated by the compiler, so
   you need to re-generate them if you have cleaned the project. The programs in
   these files are in administrative normal form (ANF), while the figures in the
   paper are not typeset in ANF for readability, as clarified in the paper.
   Similarly, we have applied the optimizations described in Section 5, so they
   do not correspond to the figures exactly. That said, there are command line
   options to disable optimization and print them in a more readable form; see
   [Understand the compilation pipeline](#understand-the-compilation-pipeline).

The following table summerizes the syntactic and naming discrepancies between
the Taype source code and the listings in the paper.

| In paper | In artifact | Comment |
| -------- | ----------- | ------- |
| `\vmathbb{1}` | `unit` | unit type |
| `\mathbb{B}` | `bool` | boolean type |
| `\mathbb{Z}` | `int` | integer type |
| `\times` | `*` | product type former |
| `\langle _,_ \rangle` | `` `(_,_) `` | oblivious pair |
| `\uparrow` | `!` | promotion |
| name with hat | prefixed by `` ` `` | e.g., `` `x `` for x with hat |
| name with tilde | prefixed by `` ~ `` | e.g., `` ~x `` for x with tilde |
| section and retraction with subscripts | use underscore | e.g., `s_list` and `r_list` |
| `\equiv` | `==` | integer equality |
| `\lambda` | `\` | lambda abstraction |
| `\Rightarrow` | `->` | separator used in lambda abstraction and case analysis |
| `case _ of _` | `case _ of _ end` | case analysis (pattern matching) |
| `\mathcal{A}` | `@` | oblivious array type |
| `\mathcal{A}(_)` | `@new` | array creation operator |
| `++` | `@concat` | array concatenation operator |
| `_(_,_)` | `@slice` | array slicing operator |
| `\mathbb{N}` | `int` | size type; we reuse the integer type for simplicity |
| `prom` with subscript | use `#` and prefixed by `~` | the promotion constructor, e.g., `~list` in Fig. 14 has constructor `~prom#list` |
| `if` with hat and subscript | use `#` and prefixed by `~` | the leaky if constructor, e.g., `~list` in Fig. 14 has constructor `~if#list` (admittedly it is a bit confusing that we use `~` here) |
| `case` with tilde and subscript | use `#` and prefixed by `~` | the leaky case analysis function, e.g., in Fig. 14 is `~case#list` |
| `if` with tilde | `~case#bool` | e.g., in Fig. 13 (a) |

We need to explain the discrepancy about `if` with tilde in a bit more detail.
The actual implementation of OIL does not treat boolean as a builtin type but
another ADT, so the leaky version of the elimination (case analysis) of boolean
is `~case#bool` instead of `~if`. In addition, the order of its branches are
swapped (as we consider `False` the first constructor and then `True`), and we
make the branches into thunks. For example, `~if b e1 e2` is actually
`~case#bool b (\_ -> e2) (\_ -> e1)`. The paper still uses the simpler version
for presentation purposes.

## Reproduce the experiment results

To reproduce Fig. 22 and 23 in the paper, we first run all the microbenchmarks:

``` sh
cd taype
# Build examples
cabal run shake
# Run all tests. Be warned: this command takes a long time (possibly more than an hour)
cabal run shake -- --round=10 run
```

This command will run each test case 10 times and take the average of the
performance statistics. The results are written to the directory
`examples/output`. This can take a long time, so you may want to test fewer
rounds, although it sacrifices some accuracy:

``` sh
cabal run shake -- --round=1 run
```

Fig. 23 in the paper also includes performance results with the tupling
optimization disabled (dotted lines). To reproduce this, run:

```sh
# Change --round option to save time
TAYPE_FLAGS=--fno-tupling cabal run shake -- --out-dir=examples/output-no-tupling --round=10 run
```

This command will run the same tests but with tupling optimization disabled, and
write the results to the directory `examples/output-no-tupling`. You may choose
to not run this experiment and generate plots without the dotted lines.

After it finishes, we open the Python notebook `taype/examples/figs.ipynb` in
the browser with code-server. This notebook plots the performance statistics and
also generates PDFs to the directory `taype/examples/figs` which we use for Fig.
22 and Fig. 23. The PDFs are `dtree-emp.pdf`, `tree-emp.pdf`, `list-emp-1.pdf`
and `list-emp2.pdf`. If you choose to not run the tests with tupling disabled,
you can modify the `configs` variable in the notebook by removing the
`"no-tupling"` element from it (there are also comments in the notebook to help
you with this). The plots it generates will now not include the dotted lines.

You can simply view these plots inside the notebook. But if you prefer not to,
you may run the Python script directly in the console, and copy the generated
PDFs to your host machine:

``` sh
cd taype/examples
python3 figs.py
```

You are most likely not getting the exact same numbers as in the paper, because
the performance of these oblivious programs vary, depending on the power of your
machine, the cryptographic instructions supported by your CPU and a lot of other
factors, let alone running them in a docker container. However, you should
observe similar curves and comparative results.

If you are interested in how the tests are done, see [Understand the
test cases](#understand-the-test-cases).

## Coq formalization of the core calculus

We have formalized the core Taype calculus in Coq (`~/taype-theories`),
including proofs of the soundness and obliviousness theorems.

To validate the formalization, run:

```sh
cd taype-theories
make clean
make
```

These commands should output two lines stating `Closed under the global
context`. These are produced from the file
`taype-theories/theories/lang_taype/metatheories.v`, indicating that both of the
key theorems have been proved without any axioms.

The following table summarizes the correspondence between the paper and the Coq
formalization:

| In paper | In artifact | Comment |
| -------- | ----------- | ------- |
| Fig. 8 | `expr`, `gdef`, `llabel`, `otval`, `oval` and `val` in `taype-theories/theories/lang_taype/syntax.v`, while weak value is `wval` in `taype-theories/theories/lang_taype/semantics.v` | |
| Fig. 9 | `step`, `ectx` and `lectx` in `taype-theories/theories/lang_taype/semantics.v` | |
| Fig. 10 | `typing` in `taype-theories/theories/lang_taype/typing.v` | |
| Theorem 3.1 (Obliviousness) | `obliviousness` in `taype-theories/theories/lang_taype/metatheories.v` | |

The `soundness` theorem is also available in
`taype-theories/theories/lang_taype/metatheories.v`.

For simplicity, our mechanization of the core calculus differs
slightly from the one presented in the paper:
- The mechanization does not include integers as a base type, similar to [Ye and
  Delaware, Oblivious Algebraic Data Types,
  POPL22](https://doi.org/10.1145/3498713)
- The mechanization includes `fold` and `unfold` operations for recursive ADTs,
  instead of the ML-style ADTs in the paper. The equivalence between these two
  styles is well-known (cf. Chapter 20 of "Types and Programming Languages").
- The mechanization has a negative elimination form for product types (i.e.
  projection) instead of positive elimination forms (i.e. case analysis). These
  two styles are well-known to be equivalent in nonlinear type systems.
- The mechanization uses *locally nameless representation* for
  binders.
- Some notational differences which should be easy to disambiguate: we use
  unicode `\mathbb{B}` instead of `bool`, for example.

## Understand the compilation pipeline

In this section, we discuss how we can inspect the different stages of the
compilation pipeline (Fig. 1). We use the tutorial `taype/examples/tutorial.tp`
as a running example, which includes a lot of comments on how to write
functionalities and oblivious types.

We compile this file by invoking the Taype compiler:

``` sh
cd taype
cabal run taype -- examples/tutorial/tutorial.tp
```

This command will generate a few files in the `examples/tutorial` directory:
- `tutorial.tpc`: the fully elaborated program in core Taype,
  corresponding to the "secure functionality" block in the "core Taype" layer in
  Fig. 1
- `tutorial.oil`: the translated OIL program, corresponding to the "core
  functionality" block in the "OIL" layer in Fig. 1
- `tutorial_conceal.oil` and `tutorial_reveal.oil`: the translated section and
  retraction functions for the conceal and reveal phases (see Section 4.3),
  corresponding to the "conceal functions" and "reveal functions" blocks in the
  "OIL" layer in Fig. 1
- `tutorial.ml`, `tutorial_conceal.ml` and `tutorial_reveal.ml`: the translated
  OCaml programs, corresponding to the "secure library" block in the "target
  language" layer in Fig. 1

If we want to inspect `tutorial.tpc` and `tutorial.oil` for understanding how
the elaboration and translation algorithms work, we should disable optimization
and print the programs in a more readable form (as opposed to ANF).

``` sh
cabal run taype -- --fno-opt --readable examples/tutorial/tutorial.tp
```

Now the generated files are much closer to the listings presented in the paper,
and we can apply the translation rules in the paper to see how the generated
code corresponds to the original one. However, do not run the experiments with
these options on, as it would be much slower. You can learn about other options
by running `cabal run taype -- --help`. Specifically, we can generate the
"prelude" file (`prelude.oil`) which contains all definitions related to builtin
types, including their leaky structures:

``` sh
cabal run taype -- --generate-prelude examples/common/prelude
```

The Taype compiler only generates OCaml code as libraries. To make a runnable
application, we also have to write the "frontends" which handle IO and other
non-oblivious business, and link the application against the oblivious libraries
and a driver (corresponding to the "target language" layer in Fig. 1). For
example, `examples/tutorial/test_elem.ml`, which includes a lot of comments,
showcases how we construct a test case as a runnable executable.

We use the [Shake build system](https://shakebuild.com/) to streamline the
process of building and testing our examples. For instance,

``` sh
# Clean the tutorial example (as we may have generated the unoptimized version with the previous commands)
cabal run shake -- clean/tutorial
# Compile the tutorial example, and its test cases
# --verbose tells shake to print out the commands being run
cabal run shake -- --verbose build/tutorial
# Run the tutorial test cases
cabal run shake -- run/tutorial
# See the supported options and targets
cabal run shake -- --help
```

## Understand the test cases

Each of our test cases is implemented as a `test_<name>.ml` file, e.g.,
`examples/tutorial/test_elem.ml`. They are compiled into executables, linked
against the two drivers, e.g., `examples/tutorial/test_elem_plaintext` and
`examples/tutorial/test_elem_emp`. These executables take an argument indicating
the partipating party, and read inputs from `stdin`. Sample inputs are available
for the tutorial example, and we can run these executables directly:

``` sh
cd taype/examples/tutorial
# Run the plaintext test case (there is only one participating party: public)
./test_elem_plaintext public < test.input
# Run the emp test case (there are two participating parties: alice and bob)
./test_elem_emp alice < test.alice.input &
./test_elem_emp bob < test.bob.input
```

As we are testing the oblivious `` `elem `` function, the input specifies the
public view, the private list from Alice, the private integer from Bob, and also
the expected output. For example, the file `test.alice.input` is:

``` text
public: 10
alice: (3 4 7)
bob:
expected: false
```

See the comments in `test_elem.ml` for more details. Note that the value of
`bob` is absent (which is 6 in `test.bob.input`), since this is the input to the
party Alice.

If the executable successfully finishes the oblivious computation, it prints out
a number for the performance statistics: the plaintext version prints out the
number of MUXes in the oblivious computation, while the emp version prints out
the running time (in microseconds). These numbers are collected for plotting.

The actual inputs for the test cases are organized in a CSV file, e.g.,
`examples/tutorial/test_elem.input.csv`. The first line is the header,
specifying which party the data comes from, and then each line specifies a test
input. For example, the header of `test_elem.input.csv` is
`public,alice,bob,expected`, while one of the test line is `10,(3 4 7),6,false`.
The test runner will launch the test programs for each party and feed them the
corresponding input. The output is then collected into another CSV file, e.g.,
`examples/output/tutorial/test_elem.emp.output.csv`. We can invoke the test runner by:

``` sh
cabal run shake -- run/tutorial
```

## Install dependencies and build the source code from scratch

If you want to install the dependencies and build the projects on your own
machine, you can check out the `README.md` files under `taype`,
`taype-driver-plaintext` and `taype-driver-emp` directories. Alternatively, the
docker file used to build this docker image is also available (`~/Dockerfile` in
the docker container or on Zenodo).
