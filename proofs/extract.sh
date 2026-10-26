#!/usr/bin/env bash
# Regenerates BookCore/{Types,Funs}.lean from book-core with Charon + Aeneas.
set -euo pipefail

AENEAS_DIR="${AENEAS_DIR:-$HOME/verif/aeneas-main}"
here="$(cd "$(dirname "$0")" && pwd)"

ln -sfn "$AENEAS_DIR/backends/lean" "$here/.aeneas"

cd "$here/../book-core"
"$AENEAS_DIR/charon/charon/target/release/charon" cargo --preset=aeneas --dest-file "$here/book_core.llbc"
"$AENEAS_DIR/src/_build/default/main.exe" -backend lean -split-files -dest "$here/BookCore" "$here/book_core.llbc"
