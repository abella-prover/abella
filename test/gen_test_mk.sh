#!/usr/bin/env bash
set -euo pipefail

find examples \( -name '*.thm' -o -name '*.thmod' \) -print0 \
  | xargs -0 bin/abella_dep.exe -a bin/abella.exe -o test/test.mk
