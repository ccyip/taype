#!/bin/bash

ROUND="${1:-5}"

set -euo pipefail

cabal run shake

cabal run shake -- --round=$ROUND --out-dir=examples/output-old-sa run/list
cabal run shake -- --round=$ROUND --out-dir=examples/output-old-sa run/tree
