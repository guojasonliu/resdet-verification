#!/usr/bin/env bash
set -euo pipefail
repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
case "$(uname -s)-$(uname -m)" in
  Darwin-arm64) platform=darwin_aarch64 ;;
  Darwin-x86_64) platform=darwin ;;
  Linux-x86_64) platform=linux ;;
  Linux-aarch64) platform=linux_aarch64 ;;
  *) platform=unsupported ;;
esac
if [[ -n "${LEAN_BIN:-}" ]]; then
  lean_bin="$LEAN_BIN"
elif [[ -x "$repo_root/tools/lean-4.24.0-$platform/bin/lake" ]]; then
  lean_bin="$repo_root/tools/lean-4.24.0-$platform/bin"
elif command -v lake >/dev/null 2>&1; then
  lean_bin="$(dirname "$(command -v lake)")"
else
  echo 'Lean is missing. Run: make fetch-lean (or install lean/lean-toolchain with elan).' >&2
  exit 1
fi
export PATH="$lean_bin:$PATH"
cd "$repo_root/lean"
version="$(lean --version)"
case "$version" in
  'Lean (version 4.24.0,'*) printf '%s\n' "$version" ;;
  *) echo "Expected pinned Lean 4.24.0; got: $version" >&2; exit 1 ;;
esac
lake build
lake env lean -DwarningAsError=true Audit.lean
