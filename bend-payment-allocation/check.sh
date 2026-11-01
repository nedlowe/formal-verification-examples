#!/usr/bin/env bash
# Everything CI checks, in order:
#   1. the proof gate: every law in LAWS.bend is proven
#   2. the demo prints exactly tests/demo.expected
#   3. each mistake in mistakes/ is blocked by the gate
#   4. the JavaScript build matches the native results
#
# Uses `bend` from PATH, or the command in $BEND (e.g. "bun ~/bend/bend2/main.ts").
set -euo pipefail
cd "$(dirname "$0")"
read -r -a bend <<< "${BEND:-bend}"

echo "== 1. proof gate"
"${bend[@]}" PROOF.bend

echo "== 2. demo output"
diff -u tests/demo.expected <("${bend[@]}" demo.bend)
echo "matches tests/demo.expected"

echo "== 3. mistakes are blocked"
for mistake in mistakes/*.bend; do
  work="$(mktemp -d)"
  cp -R . "$work"
  cp "$mistake" "$work/main.bend"
  if (cd "$work" && "${bend[@]}" PROOF.bend >/dev/null 2>&1); then
    echo "FAIL: $mistake passed the gate"; rm -rf "$work"; exit 1
  fi
  rm -rf "$work"
  echo "blocked: $mistake"
done

echo "== 4. JavaScript build"
mkdir -p build
"${bend[@]}" main.bend -o build/allocate.mjs
node node/example.mjs | diff -u tests/node.expected -
echo "matches tests/node.expected"

echo
echo "ALL CHECKS PASS"
