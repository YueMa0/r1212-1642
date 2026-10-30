#!/usr/bin/env bash
# Replay exactly the 43 upstream modules, one module per run.
set -euo pipefail
export LC_ALL=C
cd "$(dirname "$0")/.."

# An empty/partial/failed enumeration must not become a successful empty audit.
modules=()
previous=''
while IFS= read -r module || [[ -n "$module" ]]; do
  if [[ ! "$module" =~ ^RamseyIncrement\.[A-Za-z0-9_.]+$ ]] ||
     [[ -n "$previous" && ! "$previous" < "$module" ]]; then
    echo "FAIL  invalid, duplicate or unsorted upstream module: $module" >&2
    exit 1
  fi
  modules+=("$module")
  previous=$module
done < audit/upstream_modules.txt
if [[ ${#modules[@]} -ne 43 ]]; then
  echo "FAIL  expected 43 upstream modules, got ${#modules[@]}" >&2
  exit 1
fi

files=$(mktemp)
trap 'rm -f -- "$files"' EXIT
if ! find RamseyIncrement -type f -name '*.lean' \
    -not -path '*/R1212/*' -not -path '*/ThirdConnector/*' | sort > "$files"; then
  echo 'FAIL  upstream module enumeration failed' >&2
  exit 1
fi
discovered=()
while IFS= read -r file; do
  module=${file%.lean}
  discovered+=("${module//\//.}")
done < "$files"
# The `-` default matters on bash 3.2 (macOS): there `set -u` rejects an empty array,
# and the EXIT trap above would then turn the error into exit status 0.
if [[ "${modules[*]}" != "${discovered[*]-}" ]]; then
  echo "FAIL  upstream module set differs from the expected 43 (${#discovered[@]} found)" >&2
  exit 1
fi

status=0
for module in "${modules[@]}"; do
  if lake env leanchecker "$module"; then
    echo "ok    $module"
  else
    echo "FAIL  $module" >&2
    status=1
  fi
done
exit "$status"
