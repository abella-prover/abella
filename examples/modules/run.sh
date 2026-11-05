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
rm -f test/modules/*.thmodc test/modules/*.thc
rm -f test/modules/errors/*.thmodc

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
ok test/modules/Edge.thmod
bad test/modules/EdgeClosed.thm "closed and cannot be subordinated"

bad test/modules/errors/HigherOrder.thmod \
  "may not take an argument containing prop"
ok test/modules/errors/PolyValue.thmod
bad test/modules/errors/PolyValueUse.thmod "same type"
ok test/modules/errors/Unfinished.thmod
bad test/modules/errors/UnfinishedUse.thmod "unfinished theorem"
ok test/modules/errors/Internal.thmod
bad test/modules/errors/InternalUse.thmod "target-local type"
bad test/modules/errors/Collision.thmod \
  "already occurs in the declarations"
ok test/modules/errors/Staged.thmod
bad test/modules/errors/StagedUse.thmod \
  "already occurs in the declarations"
ok test/modules/errors/Statement.thmod
bad test/modules/errors/StatementUse.thmod "same statement"
