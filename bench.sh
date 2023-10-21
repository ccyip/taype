#!/bin/bash

set -euo pipefail

# FIXME: is there a better way?
# export DYLD_LIBRARY_PATH=$OPAM_SWITCH_PREFIX/lib

function go() {
  cabal run shake -- --round=5 $@
}

# No smart array
# FIXME: we need to run this separately after installing the right driver
# go --no-smart-array --out-dir=examples/output-no-smart-array run/list
# go --no-smart-array --out-dir=examples/output-no-smart-array run/tree

# No reshape guard
go clean
TAYPE_FLAGS=--fno-guard-reshape go --out-dir=examples/output-no-reshape-guard run/list
TAYPE_FLAGS=--fno-guard-reshape go --out-dir=examples/output-no-reshape-guard run/tree

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

# Compilation
go clean
go --out-dir=examples/output-compile build
go --out-dir=examples/output-compile build
go --out-dir=examples/output-compile build
go --out-dir=examples/output-compile build
go --out-dir=examples/output-compile build
