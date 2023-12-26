#!/bin/bash

set -euo pipefail

function go() {
  cabal run shake -- --round=5 $@
}

# No smart array
go clean
go --naive --out-dir=examples/output-no-smart-array run/list
go --naive --out-dir=examples/output-no-smart-array run/tree

# No reshape guard
go clean
TAYPE_FLAGS=--fno-reshape-guard go --out-dir=examples/output-no-reshape-guard run/list
TAYPE_FLAGS=--fno-reshape-guard go --out-dir=examples/output-no-reshape-guard run/tree

# No memo
go clean
TAYPE_FLAGS=--fno-memo go --out-dir=examples/output-no-memo run/list
TAYPE_FLAGS=--fno-memo go --out-dir=examples/output-no-memo run/tree
TAYPE_FLAGS=--fno-memo go --out-dir=examples/output-no-memo run/list-memo
TAYPE_FLAGS=--fno-memo go --out-dir=examples/output-no-memo run/tree-memo

# All optimization enabled
go clean
go --out-dir=examples/output-best run/list
go --out-dir=examples/output-best run/tree
go --out-dir=examples/output-best run/list-memo
go --out-dir=examples/output-best run/tree-memo

# Compilation (collect 5 runs)
#
# Do not need to clean after each compilation. Taype compiler will always get
# rerun, while OCaml compiler will not.
go clean
go --out-dir=examples/output-compile build
go --out-dir=examples/output-compile build
go --out-dir=examples/output-compile build
go --out-dir=examples/output-compile build
go --out-dir=examples/output-compile build
