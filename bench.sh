#!/bin/bash

ROUND="${1:-5}"

set -euo pipefail

function clean() {
  cabal run shake -- clean
}

function go() {
  cabal run shake -- --round=$ROUND $@
}

# No smart array
clean
go --naive --out-dir=examples/output-no-smart-array run/list
go --naive --out-dir=examples/output-no-smart-array run/tree

# No reshape guard
clean
TAYPE_FLAGS=--fno-reshape-guard go --out-dir=examples/output-no-reshape-guard run/list
TAYPE_FLAGS=--fno-reshape-guard go --out-dir=examples/output-no-reshape-guard run/tree

# No memo
clean
TAYPE_FLAGS=--fno-memo go --out-dir=examples/output-no-memo run/list
TAYPE_FLAGS=--fno-memo go --out-dir=examples/output-no-memo run/tree
TAYPE_FLAGS=--fno-memo go --out-dir=examples/output-no-memo run/list-memo
TAYPE_FLAGS=--fno-memo go --out-dir=examples/output-no-memo run/tree-memo

# All optimization enabled
clean
go --out-dir=examples/output-best run/list
go --out-dir=examples/output-best run/tree
go --out-dir=examples/output-best run/list-memo
go --out-dir=examples/output-best run/tree-memo

# Compilation
#
# Do not need to clean after each compilation. Taype compiler will always get
# rerun, while OCaml compiler will not.
clean
for ((n=0; n<$ROUND; n++)); do
  cabal run shake -- --out-dir=examples/output-compile build
done
