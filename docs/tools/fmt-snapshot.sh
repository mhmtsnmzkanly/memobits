#!/bin/bash
# Usage (from the repository root, after building target/debug/mb): docs/tools/fmt-snapshot.sh OUTDIR
# Records check/test/run output (stdout, stderr, exit status) of every example
# project and analyze/ownership output of the standalone analysis inputs.
set -u
out=$1
mkdir -p "$out"
mb=target/debug/mb
for manifest in examples/guide/project.toml examples/topics/*/project.toml examples/apps/*/project.toml; do
  name=$(echo "$manifest" | sed 's|/project.toml||; s|/|__|g')
  for cmd in check test run; do
    $mb $cmd --project "$manifest" >"$out/$name.$cmd.out" 2>"$out/$name.$cmd.err"
    echo "exit $?" >>"$out/$name.$cmd.out"
  done
done
for f in examples/analysis/*.mb; do
  name=$(echo "$f" | sed 's|/|__|g')
  for cmd in analyze ownership; do
    $mb $cmd "$f" >"$out/$name.$cmd.out" 2>"$out/$name.$cmd.err"
    echo "exit $?" >>"$out/$name.$cmd.out"
  done
done
