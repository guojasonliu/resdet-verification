#!/usr/bin/env bash
# Project-local Lean; no profile changes, global install, or CloudLab access.
set -euo pipefail
repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
version=4.24.0
case "$(uname -s)-$(uname -m)" in
  Darwin-arm64)
    platform=darwin_aarch64
    checksum=17ee554702c199fc03f37b1c3708245671c93f5d932dcff55a03fa6cdb5e5adf ;;
  Darwin-x86_64)
    platform=darwin
    checksum=a5ef0fb0e14645eaa0e60bc6ba39a07e7deeeec73dc93ce7195b837eb9de2c9f ;;
  Linux-x86_64)
    platform=linux
    checksum=b14f5e5159219dd1a1956c3b806813319f5e94ccd5bdfd56f54520609a5bb5ec ;;
  Linux-aarch64)
    platform=linux_aarch64
    checksum=237f8ef43fb40d16681871fb04b2c56f023afc02a5a3877831d35dd493823c23 ;;
  *) echo 'Unsupported platform; install the pinned lean/lean-toolchain using elan.' >&2; exit 1 ;;
esac
destination="$repo_root/tools/lean-$version-$platform"
if [[ -x "$destination/bin/lean" && -x "$destination/bin/lake" ]]; then
  "$destination/bin/lean" --version
  exit 0
fi
if [[ -e "$destination" ]]; then
  echo "Incomplete toolchain at $destination; refusing to overwrite it." >&2
  exit 1
fi
mkdir -p "$repo_root/tools"
archive="$(mktemp "$repo_root/tools/lean-download.XXXXXX")"
trap 'rm -f "$archive"' EXIT
curl --fail --location --retry 3 --connect-timeout 20 \
  "https://github.com/leanprover/lean4/releases/download/v$version/lean-$version-$platform.tar.zst" \
  --output "$archive"
if command -v sha256sum >/dev/null 2>&1; then
  actual="$(sha256sum "$archive" | awk '{print $1}')"
else
  actual="$(shasum -a 256 "$archive" | awk '{print $1}')"
fi
if [[ "$actual" != "$checksum" ]]; then
  echo "Lean archive checksum mismatch: expected $checksum, got $actual" >&2
  exit 1
fi
tar -xf "$archive" -C "$repo_root/tools"
"$destination/bin/lean" --version
