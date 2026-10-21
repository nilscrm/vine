#!/usr/bin/env bash
# Runs tests/programs and vine/examples on the frames runtime, comparing their
# output with the (IVM) snapshots in tests/snaps (or with IVM's output, for
# programs without one), and summarizes why the failing ones fail.
#
# Usage: tests/frames.sh [name-filter]
#
# Each program's output and stderr are kept in $OUT (default
# target/frames-tests), as `<kind>-<name>.out.<ext>` and `<kind>-<name>.stats`.
# Programs are killed after $TIMEOUT seconds (default 20).

cd "$(git rev-parse --show-toplevel)" || exit 1
cargo build -q --release --bin vine || exit 1
VINE=target/release/vine
OUT=${OUT:-target/frames-tests}
TIMEOUT=${TIMEOUT:-20}
mkdir -p "$OUT"
filter=$1
pass=0
fail=0
failed=()

# The value of a `// @key value` directive in a test's config file.
directive() { # file key default
  if grep -qE "^(//|#) @$2( |$)" "$1" 2>/dev/null; then
    grep -m1 -E "^(//|#) @$2( |$)" "$1" | sed -E "s/^(\/\/|#) @$2 ?//"
  else
    echo "$3"
  fi
}

run_one() { # kind name vi config
  local kind=$1 name=$2 vi=$3 config=$4
  [ -n "$filter" ] && [[ "$name" != *$filter* ]] && return
  local build input ext
  build=$(directive "$config" build "")
  input=tests/input/$(directive "$config" input empty)
  ext=$(directive "$config" output txt)
  local expected=tests/snaps/$kind/$name/output.$ext
  local out=$OUT/$kind-$name.out.$ext
  if [ ! -f "$expected" ]; then
    # Some outputs are checked by tests/verify instead of a snapshot; compare
    # with IVM's output.
    expected=$OUT/$kind-$name.ivm.$ext
    # shellcheck disable=SC2086
    $VINE run --no-stats "$vi" $build <"$input" >"$expected" 2>/dev/null
  fi
  # `perl -e alarm` is a portable `timeout`.
  # shellcheck disable=SC2086
  perl -e 'alarm shift; exec @ARGV' "$TIMEOUT" \
    $VINE run --frames --no-stats "$vi" $build <"$input" >"$out" 2>"$OUT/$kind-$name.stats"
  if [ -f "$expected" ] && cmp -s "$out" "$expected"; then
    pass=$((pass + 1))
  else
    fail=$((fail + 1))
    failed+=("$kind/$name")
  fi
}

for p in tests/programs/*; do
  name=$(basename "$p")
  name=${name%.vi}
  if [ -d "$p" ]; then config=$p/$name.vi; else config=$p; fi
  run_one programs "$name" "$p" "$config"
done
for p in vine/examples/*.vi; do
  name=$(basename "$p" .vi)
  run_one examples "$name" "$p" "tests/examples/$name"
done
rm -f vine-file-test.txt # written by tests/programs/file.vi

echo "passed: $pass, failed: $fail"
for f in "${failed[@]}"; do
  reason=$(grep -m1 -oE "(error|panicked at).{0,110}" "$OUT/${f/\//-}.stats")
  echo "  FAIL $f${reason:+: $reason}"
done
echo
echo "failing programs per error:"
for f in "${failed[@]}"; do
  grep -oE "(not yet supported by the frames backend: [^(]{0,60}|deadlock|hole read more than once|panicked at [a-z/._]+|unreachable code: [A-Za-z]+|has infinite size|invalid operands to \`[a-z0-9:_]+\`)" \
    "$OUT/${f/\//-}.stats" | sort -u
done | sort | uniq -c | sort -rn
[ "$fail" -eq 0 ]
