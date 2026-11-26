#!/usr/bin/env bash
# Usage: [MBBIN=<prebuilt mb>] [ROOT=<repo root>] docs/tools/equivalence.sh <outdir>
# Captures check/run/test/build/standalone-run/syntax/analyze/ownership output and Wasm
# hashes for every example project, to diff two compiler builds (`diff -r -x build.log A B`).
# Always runs from ROOT so embedded source paths match. With MBBIN (e.g. a build of the
# previous commit made in another directory) no build is done and that binary runs the
# same example sources.
set -u
ROOT=${ROOT:-$(cd "$(dirname "$0")/../.." && pwd)}
OUT=$(mkdir -p "$1" && cd "$1" && pwd)
cd "$ROOT"
if [ -z "${MBBIN:-}" ]; then
  cargo build -j1 -p memobits-cli >"$OUT/build.log" 2>&1 || { echo "build failed"; exit 1; }
  MB=target/debug/mb
else
  MB=$MBBIN
fi
WORK=target/equivalence-work   # fixed path so printed paths are identical across runs
rm -rf "$WORK"; mkdir -p "$WORK"
cap() { # name, args...
  local n=$1; shift
  "$@" >"$OUT/$n.stdout" 2>"$OUT/$n.stderr"; echo $? >"$OUT/$n.exit"
}
for p in examples/guide/project.toml examples/topics/*/project.toml examples/apps/*/project.toml; do
  d=$(echo "$(dirname "$p")" | tr / _)
  cap "$d.check" $MB check --project "$p"
  cap "$d.run" $MB run --project "$p"
  cap "$d.test" $MB test --project "$p"
  cap "$d.build" $MB build --project "$p" --output "$WORK/$d.wasm"
  if [ -f "$WORK/$d.wasm" ]; then cap "$d.runwasm" $MB run "$WORK/$d.wasm"; fi
  m=$(dirname "$p")/src/main.mb
  if [ -f "$m" ]; then
    for c in syntax analyze ownership; do cap "$d.$c" $MB $c "$m"; done
  fi
done
(cd "$WORK" && sha256sum *.wasm 2>/dev/null) >"$OUT/wasm.sha256"
rm -rf "$WORK"
