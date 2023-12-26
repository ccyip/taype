#!/bin/bash

set -euo pipefail

cabal run shake

cabal run shake -- --round=5 --out-dir=examples/output-old-sa run/list
cabal run shake -- --round=5 --out-dir=examples/output-old-sa run/tree
