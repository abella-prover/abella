#!/usr/bin/env bash
set -euo pipefail

find examples -name '*.thm' -not -path 'examples/modules/*' -print0 \
  | xargs -0 bin/abella_dep.exe -a bin/abella.exe -o test/test.mk
