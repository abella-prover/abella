#!/usr/bin/env bash
set -euo pipefail

abella="${1:-bin/abella.exe}"
out="${TMPDIR:-/tmp}/abella-thmod-example.$$"
trap 'rm -f "$out"' EXIT

ok() {
  if ! "$abella" "$1" >/dev/null 2>&1; then
    echo "FAILED: $1" >&2
    "$abella" "$1" >&2 || true
    exit 1
  fi
}

bad() {
  if "$abella" "$1" >"$out" 2>&1; then
    echo "EXPECTED FAILURE: $1" >&2
    cat "$out" >&2
    exit 1
  fi
  if ! grep -q "$2" "$out"; then
    echo "WRONG ERROR: $1 (expected: $2)" >&2
    cat "$out" >&2
    exit 1
  fi
}

rm -f examples/modules/*.thmodc examples/modules/*.thc
rm -f examples/modules/errors/*.thmodc

ok examples/modules/List.thmod
ok examples/modules/ListUse.thm
ok examples/modules/Box.thmod
ok examples/modules/BoxUse.thmod
ok examples/modules/Nested.thmod
ok examples/modules/NestedUse.thmod
ok examples/modules/Eq.thmod
ok examples/modules/EqUse.thmod
ok examples/modules/EqUseDecl.thmod
ok examples/modules/PropKey.thmod
ok examples/modules/PropKeyUse.thmod
ok examples/modules/Keys.thmod
ok examples/modules/KeysUse.thmod
ok examples/modules/Edge.thmod
bad examples/modules/EdgeClosed.thm "closed and cannot be subordinated"

bad examples/modules/errors/HigherOrder.thmod \
  "may not take an argument containing prop"
ok examples/modules/errors/PolyValue.thmod
bad examples/modules/errors/PolyValueUse.thmod "same type"
ok examples/modules/errors/Unfinished.thmod
bad examples/modules/errors/UnfinishedUse.thmod "unfinished theorem"
ok examples/modules/errors/Internal.thmod
bad examples/modules/errors/InternalUse.thmod "target-local type"
bad examples/modules/errors/Collision.thmod \
  "already occurs in the declarations"
ok examples/modules/errors/Staged.thmod
bad examples/modules/errors/StagedUse.thmod \
  "already occurs in the declarations"
ok examples/modules/errors/Statement.thmod
bad examples/modules/errors/StatementUse.thmod "same statement"
