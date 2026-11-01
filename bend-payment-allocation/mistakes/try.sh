#!/usr/bin/env bash
# Try one of the mistakes: swap it in for main.bend in a scratch copy of the
# project, run the proof gate, then run the demo to show what the change
# would have paid. Nothing in the project itself is modified.
#
#   ./mistakes/try.sh mistakes/naive-rounding.bend
#
# Uses `bend` from PATH, or the command in $BEND (e.g. "bun ~/bend/bend2/main.ts").
set -euo pipefail

here="$(cd "$(dirname "$0")/.." && pwd)"
mistake="$(cd "$(dirname "$1")" && pwd)/$(basename "$1")"
read -r -a bend <<< "${BEND:-bend}"

work="$(mktemp -d)"
trap 'rm -rf "$work"' EXIT
cp -R "$here"/. "$work"
cp "$mistake" "$work/main.bend"
cd "$work"

echo "== bend PROOF.bend   (with $(basename "$mistake") as main.bend)"
if "${bend[@]}" PROOF.bend; then
  echo "!! the gate let this change through"
  exit 1
fi
echo
echo "== the gate blocked it. What it would have paid:"
echo
"${bend[@]}" demo.bend
