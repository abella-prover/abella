#!/usr/bin/env bash

# Compile the positive reasoning-module examples in order and check the
# expected failures in test/modules. Run from the repository root:
#   bash examples/modules/run.sh _build/default/bin/abella.exe
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
rm -f examples/modules/*.out
rm -f test/modules/*.thmodc test/modules/*.thc
rm -f test/modules/*.out
rm -f test/modules/errors/*.thmodc test/modules/errors/*.out

ok examples/modules/List.thmod
ok examples/modules/ListUse.thm
ok examples/modules/ShowModule.thm
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
bad test/modules/EdgeClosed.thm "closed and cannot be subordinated"

bad test/modules/errors/HigherOrder.thmod \
  "may not take an argument containing prop"
bad test/modules/errors/PolyValueMismatch.thmod "same type"
bad test/modules/errors/UnfinishedAxiom.thmod "unfinished theorem"
bad test/modules/errors/InternalKindKey.thmod "target-local type"
bad test/modules/errors/Collision.thmod \
  "already occurs in the declarations"
bad test/modules/errors/StagedCollision.thmod \
  "already occurs in the declarations"
bad test/modules/errors/StatementMismatch.thmod "same statement"
